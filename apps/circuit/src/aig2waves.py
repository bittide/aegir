# Copyright 2023 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Generate an isomorphic bittide app in the waves dialect from a Yosys AIG netlist."""
import logging
import sys
import json
import textwrap

INDENT = 4 * ' '
AND_CELL = '$_AND_'
NOT_CELL = '$_NOT_'
DFF_CELL = '$_DFF_P_'

class LogicCone:

  def __init__(self, design, cone_cells):
    assert cone_cells
    self.design = design
    self.cone_cells = list(cone_cells)
    self._cone_cells_set = set(self.cone_cells)
    _, self.output_signal = next(
        self.design.iter_cell_outputs(self.cone_cells[0]))
    self._primary_inputs = set(self._iter_all_cone_inputs()).difference(
        set(self._iter_all_cone_outputs()))
    seen = set()
    self._primary_inputs_ord = []
    for signal in self._iter_all_cone_inputs():  # enforces iteration order
      if signal in self._primary_inputs and signal not in seen:
        self._primary_inputs_ord.append(signal)
        seen.add(signal)

  def _iter_all_cone_inputs(self):
    return (signal for cell in self.cone_cells
            for _, signal in self.design.iter_cell_inputs(cell))

  def _iter_all_cone_outputs(self):
    return (signal for cell in self.cone_cells
            for _, signal in self.design.iter_cell_outputs(cell))

  def iter_input_signals(self):
    return iter(self._primary_inputs_ord)

  def __repr__(self):
    return f'LogicCone({",".join(str(x) for x in self.iter_input_signals())})'

  def statements(self, *, exclude_as_primary_inputs=set()):
    statements = []
    primary_inputs = self._primary_inputs.difference(
        set(exclude_as_primary_inputs))

    def s(port, conn):
      signal = conn[port][0]
      if signal == '0':
        return 'false'
      elif signal == '1':
        return 'true'
      else:
        signal_unwrap = '.unwrap_or(false)' if signal in primary_inputs else ''
        return f'b{signal}{signal_unwrap}'

    def _rec(signal):
      try:
        cell_name = self.design.cell_by_output(signal)
      except KeyError:
        return
      if cell_name not in self._cone_cells_set:
        return
      for _, input_signal in self.design.iter_cell_inputs(cell_name):
        _rec(input_signal)

      cell = self.design.cell_attrs_by_name(cell_name)
      conn = cell['connections']
      if cell['type'] == AND_CELL:
        statements.append(
            f'let b{conn["Y"][0]} = {s("A", conn)} && {s("B", conn)};')
      elif cell['type'] == NOT_CELL:
        statements.append(f'let b{conn["Y"][0]} = !{s("A", conn)};')
      else:
        raise ValueError('Cell not supported.')

    _rec(self.output_signal)
    return statements


class DesignModule:

  def __init__(self, design, *, clk_name='clk'):
    self.design = design
    self.clk_name = clk_name

    for cell_name in self.iter_cells():
        cell_attr = self.cell_attrs_by_name(cell_name)
        if cell_attr['type'] not in (AND_CELL, NOT_CELL, DFF_CELL):
            raise ValueError(f'Unsupported cell {cell_attr["type"]} in design.')

    self._cell_by_output = {}
    for cell_name in self.iter_cells():
      for _, signal in self.iter_cell_outputs(cell_name):
        self._cell_by_output[signal] = cell_name

    self._input_signals = set()
    self._output_signals = set()
    for port_name, port_attr in self.design['ports'].items():
      if port_attr['direction'] == 'input':
        for signal in port_attr['bits']:
          self._input_signals.add(signal)
      if port_attr['direction'] == 'output':
        for signal in port_attr['bits']:
          self._output_signals.add(signal)

  def iter_ports(self):
    return iter(self.design['ports'].items())

  def cell_attrs_by_name(self, cell_name):
    return self.design['cells'][cell_name]

  def _iter_cell_ports_by_direction(self, cell_name, direction):
    cell_attrs = self.cell_attrs_by_name(cell_name)
    for port_name, port_dir in cell_attrs['port_directions'].items():
      if port_dir == direction:
        yield port_name, cell_attrs['connections'][port_name][0]

  def iter_cells(self):
    return iter(self.design['cells'])

  def iter_cell_inputs(self, cell_name):
    yield from self._iter_cell_ports_by_direction(cell_name, 'input')

  def iter_cell_outputs(self, cell_name):
    yield from self._iter_cell_ports_by_direction(cell_name, 'output')

  def cell_by_output(self, output):
    return self._cell_by_output[output]

  def is_input_signal(self, signal):
    return signal in self._input_signals

  def is_output_signal(self, signal):
    return signal in self._output_signals

  def iter_input_signals(self):
    return iter(self._input_signals)

  def iter_output_signals(self):
    return iter(self._output_signals)

  def is_register_cell(self, cell_name):
    cell_attrs = self.cell_attrs_by_name(cell_name)
    return cell_attrs['type'] == DFF_CELL

  def is_register_Q(self, signal):
    try:
      cell_name = self.cell_by_output(signal)
    except KeyError:
      return False
    if not self.is_register_cell(cell_name):
      return False
    cell_attrs = self.cell_attrs_by_name(cell_name)
    return cell_attrs['connections']['Q'][0] == signal

  def is_constant_signal(self, signal):
    return signal == '0' or signal == '1'

  def signal_logic_cone(self, signal):
    visited = set()
    logic_cone = []

    def _rec(signal):
      if self.is_constant_signal(signal) or self.is_input_signal(
          signal) or self.is_register_Q(signal) or signal in visited:
        return
      visited.add(signal)
      cell_name = self.cell_by_output(signal)
      logic_cone.append(cell_name)
      for _, input_signal in self.iter_cell_inputs(cell_name):
        _rec(input_signal)

    _rec(signal)
    if logic_cone:
      return LogicCone(self, logic_cone)
    else:
      return None

  def create_input_actions(self, stimulus):
    input_actions = []
    for port_name, port_attrs in self.iter_ports():
      if port_name == self.clk_name:
        continue
      if port_attrs['direction'] == 'input':
        input_actions.append(
            InputAction(
                design=self,
                name=f'in_{port_name}',
                outputs=port_attrs['bits'],
                stimulus=stimulus[port_name]))
    return input_actions

  def create_output_actions(self):
    output_actions = []
    for port_name, port_attrs in self.iter_ports():
      if port_name == self.clk_name:
        continue
      if port_attrs['direction'] == 'output':
        output_actions.append(
            OutputAction(
                design=self,
                name=f'out_{port_name}',
                outputs=port_attrs['bits']))
    return output_actions

  def create_register_actions(self):
    register_actions = []
    for cell_name in self.iter_cells():
      if self.is_register_cell(cell_name):
        register_actions.append(
            RegisterAction(design=self, cell_name=cell_name))
    return register_actions


class StateType:
  BOOL = 1
  U8 = 2
  U16 = 3
  U32 = 4
  U64 = 5

  def rust_value(self, v):
    if self.type == self.BOOL:
      return 'true' if v else 'false'
    else:
      return f'{v}'

  def rust_name(self):
    return {
        self.BOOL: 'bool',
        self.U8: 'u8',
        self.U16: 'u16',
        self.U32: 'u32',
        self.U64: 'u64',
    }[self.type]

  def __init__(self, bits_count):
    self.type = self.bits_to_type(bits_count)

  def unpack_src(self, dst, arity, src):
    if self.type == self.BOOL:
      return [f'b{dst[0]}_{k} = {src};' for k in range(arity[dst[0]])]
    else:
      return [
          f'b{bit}_{k} = (({src} >> {i}) & 1) != 0;'
          for i, bit in enumerate(dst)
          for k in range(arity[bit])
      ]

  def pack_dst(self, dst, src):
    def fmt(bit):
      if bit in ('false', 'true'):
        return bit
      else:
        return f'b{bit}'

    if self.type == self.BOOL:
      return [f'{dst} = {fmt(src[0])};']
    else:
      return [f'{dst} = 0;'] + [
          f'{dst} |= {self.rust_name()}::from({fmt(bit)}) << {i};'
          for i, bit in enumerate(src)
      ]

  @classmethod
  def bits_to_type(cls, bits_count):
    if bits_count == 1:
      return cls.BOOL
    elif bits_count <= 8:
      return cls.U8
    elif bits_count <= 16:
      return cls.U16
    elif bits_count <= 32:
      return cls.U32
    elif bits_count <= 64:
      return cls.U64
    else:
      raise ValueError(
          'Unsupported port type of length {:d} bits.'.format(bits_count))


class InputAction:

  def __init__(self, *, design, name, outputs, stimulus):
    self.design = design
    self.name = name
    self.outputs = list(outputs)
    self.output_counts = {output: 0 for output in self.outputs}
    self.stimulus = list(stimulus)

  def __repr__(self):
    return f'InputAction({self.name}, {self.outputs})'

  def iter_outputs(self):
    return iter(self.outputs)

  def set_output_counts(self, output, count):
    self.output_counts[output] = count

  def iter_outputs_typed(self):
    return (f'b{bit}_{k}: bool' for bit in self.outputs
            for k in range(self.output_counts[bit]))

  def to_waves_action(self, *, app_spec='app_spec', name=''):
    state_type = StateType(len(self.outputs))
    decl = f'let {name or self.name} = waves::action!("{name or self.name}" in {app_spec}'
    indent = []
    indent.append(f'(state: u32)')
    indent.append(f'()')
    indent.append('-> ')
    indent.append('(' + ', '.join(self.iter_outputs_typed()) + ')')
    indent.append(f'{{ u32::pack(&0).into_boxed_bitslice() }}')
    indent.append(f'{self.name});')
    indent = textwrap.indent('\n'.join(indent), INDENT)
    return '\n'.join((decl, indent))

  def to_waves(self):
    state_type = StateType(len(self.outputs))
    output_assignments = state_type.unpack_src(self.outputs, self.output_counts,
                                               'STIMULUS[state as usize]')
    output_assignments.append('state = (state + 1) % STIMULUS.len() as u32;')
    newline = '\n'
    return f"""
waves::action_fn! {{
    {self.name}
    (state: u32)
    ()
    ->
    ({", ".join(self.iter_outputs_typed())})
    {{
        const STIMULUS: [{state_type.rust_name()}; {len(self.stimulus)}] = [
{textwrap.indent(f",{newline}".join((state_type.rust_value(v) for v in self.stimulus)), 3*INDENT)}
        ];
{textwrap.indent(f"{newline}".join(output_assignments), 2*INDENT)}
    }}
}}
"""


class OutputAction:

  def __init__(self, *, design, name, outputs):
    self.design = design
    self.name = name
    self.outputs = list(outputs)

  def __repr__(self):
    return f'OutputAction({self.name}, {self.outputs})'

  def iter_inputs(self):
    for output_signal in self.outputs:
      logic_cone = self.design.signal_logic_cone(output_signal)
      if logic_cone:
        yield from logic_cone.iter_input_signals()
      elif not self.design.is_constant_signal(output_signal):
        yield output_signal

  def iter_inputs_typed(self):
    return (f'b{signal}: Option<bool>' for signal in self.iter_inputs())

  def to_waves_action(self, *, app_spec='app_spec', name=''):
    state_type = StateType(len(self.outputs))
    decl = f'let {name or self.name} = waves::action!("{name or self.name}" in {app_spec}'
    indent = []
    indent.append(f'(state: {state_type.rust_name()})')
    indent.append('(' + ', '.join(self.iter_inputs_typed()) + ')')
    indent.append('-> ')
    indent.append(f'()')
    indent.append(
        f'{{ {state_type.rust_name()}::pack(&{state_type.rust_value(0)}).into_boxed_bitslice() }}'
    )
    indent.append(f'{self.name});')
    indent = textwrap.indent('\n'.join(indent), INDENT)
    return '\n'.join((decl, indent))

  def to_waves(self):
    state_type = StateType(len(self.outputs))
    output_assignments = []
    outputs = []
    for output_signal in self.outputs:
      logic_cone = self.design.signal_logic_cone(output_signal)
      if logic_cone:
        outputs.append(output_signal)
        for stmt in logic_cone.statements():
          output_assignments.append(stmt)
      elif not self.design.is_constant_signal(output_signal):
        outputs.append(f'{output_signal}.unwrap_or(false)')
      else:
        outputs.append('false' if output_signal == '0' else 'true')
    state_pack = state_type.pack_dst('state', outputs)

    newline = '\n'
    return f"""
waves::action_fn! {{
    {self.name}
    (state: {state_type.rust_name()})
    ({", ".join(self.iter_inputs_typed())})
    ->
    ()
    {{
{textwrap.indent(f"{newline}".join(output_assignments), 2*INDENT)}
{textwrap.indent(f"{newline}".join(state_pack), 2*INDENT)}
    }}
}}
"""


class RegisterAction:

  def __init__(self, *, design, cell_name):
    self.design = design
    self.cell_name = cell_name
    assert self.design.is_register_cell(cell_name)
    Q_port, self.Q_signal = next(self.design.iter_cell_outputs(cell_name))
    assert Q_port == 'Q'
    D_port, self.D_signal = next(
        ((name, bit)
         for name, bit in self.design.iter_cell_inputs(cell_name)
         if name == 'D'))
    assert D_port == 'D'
    self.name = f'reg_b{self.Q_signal}'
    self.output_count = 0

  def iter_inputs(self):
    logic_cone = self.design.signal_logic_cone(self.D_signal)
    if logic_cone:
      for signal in logic_cone.iter_input_signals():
        if signal != self.Q_signal:
          yield signal
    else:
      yield signal

  def set_output_counts(self, output, count):
    assert output == self.Q_signal
    self.output_count = count

  def iter_inputs_typed(self):
    return (f'b{signal}: Option<bool>' for signal in self.iter_inputs())

  def iter_outputs_typed(self):
    return (f'b{self.Q_signal}_{k}: bool' for k in range(self.output_count))

  def iter_outputs(self):
    return iter((self.Q_signal,))

  def __repr__(self):
    return f'RegisterAction({self.Q_signal})'

  def to_waves_action(self, *, app_spec='app_spec', name=''):
    decl = f'let {name or self.name} = waves::action!("{name or self.name}" in {app_spec}'
    indent = []
    indent.append('(state: bool)')
    indent.append('(' + ', '.join(self.iter_inputs_typed()) + ')')
    indent.append('-> ')
    indent.append(f'({", ".join(self.iter_outputs_typed())})')
    indent.append(f'{{ bool::pack(&false).into_boxed_bitslice() }}')
    indent.append(f'{self.name});')
    indent = textwrap.indent('\n'.join(indent), INDENT)
    return '\n'.join((decl, indent))

  def to_waves(self):
    state_type = StateType(1)
    state_unpack = state_type.unpack_src([self.Q_signal],
                                         {self.Q_signal: self.output_count},
                                         'state')

    output_assignments = [f'let b{self.Q_signal} = state;']
    logic_cone = self.design.signal_logic_cone(self.D_signal)
    if logic_cone:
      output_assignments.extend(
          logic_cone.statements(exclude_as_primary_inputs={self.Q_signal}))

    state_pack = state_type.pack_dst('state', [self.D_signal])
    newline = '\n'
    return f"""
waves::action_fn! {{
    {self.name}
    (state: {state_type.rust_name()})
    ({", ".join(self.iter_inputs_typed())})
    ->
    ({", ".join(self.iter_outputs_typed())})
    {{
{textwrap.indent(f"{newline}".join(output_assignments), 2*INDENT)}
{textwrap.indent(f"{newline}".join(state_pack), 2*INDENT)}
{textwrap.indent(f"{newline}".join(state_unpack), 2*INDENT)}
    }}
}}
"""


def create_builder_fn(input_actions, register_actions, output_actions):
  output_by_action = {}
  for action in input_actions + register_actions:
    for output in action.iter_outputs():
      output_by_action[output] = action

  result = []
  result.append('pub fn build_app() -> Application {')
  result.append(
      textwrap.indent('let mut app_spec = Application::new();', INDENT))

  for action in input_actions + register_actions + output_actions:
    result.append(textwrap.indent(action.to_waves_action(), INDENT))

  output_idx = {}
  for dst_action in register_actions + output_actions:
    for input in dst_action.iter_inputs():
      src_action = output_by_action[input]
      k = output_idx.get(input, 0)
      result.append(
          textwrap.indent(
              f'waves::link!({src_action.name} b{input}_{k} -> {dst_action.name} b{input} in app_spec);',
              INDENT))
      output_idx[input] = output_idx.get(input, 0) + 1
  result.append(textwrap.indent('app_spec', INDENT))
  result.append('}')
  return '\n'.join(result)


def read_json(json_path):
  with open(json_path) as json_file:
    return json.load(json_file)


def main():
  design = read_json(sys.argv[1])
  stimulus = read_json(sys.argv[2])
  output_path = sys.argv[3]

  if len(design['modules']) != 1:
    raise ValueError('Design should have a single module, flatten hierarchy.')
  module_name, design_module = design['modules'].popitem()
  dm = DesignModule(design_module)

  input_actions = dm.create_input_actions(stimulus)
  output_actions = dm.create_output_actions()
  register_actions = dm.create_register_actions()

  output_counts = {}
  for action in output_actions + register_actions:
    for output in action.iter_inputs():
      output_counts[output] = output_counts.get(output, 0) + 1
  for action in input_actions + register_actions:
    for output in action.iter_outputs():
      action.set_output_counts(output, output_counts[output])
  build_fn = create_builder_fn(input_actions, register_actions, output_actions)

  with open(output_path, 'w') as out_file:
    print("""
#![allow(warnings, unused)]

use bits::*;
use platform::Application;
use platform::specs::ApplicationNode;
""", file=out_file)
    for action in input_actions + output_actions + register_actions:
      print(action.to_waves(), file=out_file)
    print(build_fn, file=out_file)


if __name__ == '__main__':
  logging.basicConfig(level=logging.DEBUG)
  main()
