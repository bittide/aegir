// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::specs::SystemContext;

use super::*;
use bitvec::boxed::BitBox;
use bitvec::prelude::*;
use bitvec::slice::BitSlice;
use std::convert::{TryFrom, TryInto};

/**
 * A fan_in consumes N inputs of T and produces 1 output of [Option<T>; N].
 *
 * This is used in the financial exchange, for example, to aggregate the traders together.
 */
pub fn fan_in<
    Type: bits::Bits,
    TypeArr: bits::Bits + TryFrom<Vec<Option<Type>>>,
    const LENGTH: usize,
    /*
    You may be wondering:
    "Sam, why take `TypeArr` as a type parameter? Why not just write `[Option<Type>; LENGTH]` in its stead?"
    But alas, the answer is Rust.
    When I take `Type` as a type-parameter, we require that it impls bits::Bits.
    When I write `[Option<Type>; LENGTH]`, Rust cannot guarantee that this also impls bits::Bits.
    Even if it happens to when I use it.
    Actually, only arrays of 32 or less impl bits::Bits, and there is no way to say "all arrays of
    any size impl bits::Bits".
    So, the user has to pass `<Type, [Option<Type>; LENGTH], LENGTH>` rather than just `<Type, Length>`,
    and I will ask Rust to make sure `TypeArr` impls `bits::Bits`;
    A small price to pay to avoid writing `fan_in` as a macro.
    */
>(
    loopback: LoopbackRef,
    inputs_bits: &[InputFrameRef],
    outputs_bits: &mut [OutputFrameRef],
    _sys: &dyn SystemContext,
) where
    <TypeArr as TryFrom<Vec<std::option::Option<Type>>>>::Error: std::fmt::Debug,
{
    assert_eq!(
        inputs_bits.len(),
        LENGTH,
        "Wrong number of inputs to fan_in; should be {}",
        LENGTH
    );
    assert_eq!(
        outputs_bits.len(),
        1,
        "Wrong number of outputs from fan_in; should be 1"
    );
    assert!(loopback.is_none(), "fan_in should not have loopback state");

    let output: TypeArr = inputs_bits
        .iter()
        .map(|opt_input_bits| {
            opt_input_bits.map(|input_bits| Type::unpack(input_bits.as_bitslice()))
        })
        .collect::<Vec<Option<Type>>>()
        .try_into()
        .unwrap();

    output.pack_to(&mut outputs_bits[0].data);
    outputs_bits[0].valid = true;
}

/**
 * A fan_out consumes 1 input of [Option<T>; N] and produces N outputs of T.
 */
pub fn fan_out<
    Type: bits::Bits,
    TypeArr: bits::Bits + TryFrom<Vec<Option<Type>>> + IntoIterator<Item = Option<Type>>,
    const LENGTH: usize,
>(
    loopback: LoopbackRef,
    inputs_bits: &[InputFrameRef],
    outputs_bits: &mut [OutputFrameRef],
    _sys: &dyn SystemContext,
) where
    <TypeArr as TryFrom<Vec<std::option::Option<Type>>>>::Error: std::fmt::Debug,
{
    assert_eq!(
        inputs_bits.len(),
        1,
        "Wrong number of inputs to fan_out; should be 1"
    );
    assert_eq!(
        outputs_bits.len(),
        LENGTH,
        "Wrong number of outputs from fan_out; should be {}",
        LENGTH
    );
    assert!(loopback.is_none(), "fan_out should not have loopback state");

    let outputs: TypeArr = inputs_bits[0]
        .map(|input_bits| TypeArr::unpack(input_bits))
        .unwrap_or_else(|| {
            vec![0usize; LENGTH]
                .iter()
                .map(|_| None)
                .collect::<Vec<Option<Type>>>()
                .try_into()
                .unwrap()
        });

    outputs_bits
        .iter_mut()
        .zip(outputs.into_iter())
        .for_each(|(output_bits, output)| {
            if let Some(real_output) = output {
                real_output.pack_to(&mut output_bits.data);
                output_bits.valid = true;
            } else {
                output_bits.valid = false;
            }
        });
}

/**
 * Outputs the data stored in loopback eternally.
 *
 * The loopback[0] indicates whether loopback[1..] stores valid data.
 */
pub fn source(
    loopback: LoopbackRef,
    input: &[InputFrameRef],
    output: &mut [OutputFrameRef],
    _sys: &dyn SystemContext,
) {
    assert_eq!(input.len(), 0);
    assert_eq!(output.len(), 1);

    let loopback_bits = loopback.expect("Must seed loopback with the send value");
    output[0].valid = loopback_bits[0];
    output[0].data.copy_from_bitslice(&loopback_bits[1..]);
}

/**
 * Stores its input in loopback, to be examined outside the simulation.
 *
 * The loopback[0] indicates whether loopback[1..] stores valid data.
 *
 * Note that you *must* supply a loopback buffer whose size is equal to the size of the input + 1.
 */
pub fn stateful_sink(
    loopback: LoopbackRef,
    input: &[InputFrameRef],
    output: &mut [OutputFrameRef],
    _sys: &dyn SystemContext,
) {
    assert_eq!(input.len(), 1);
    assert_eq!(output.len(), 0);

    let loopback_bits = &mut loopback.expect("Must seed loopback with an empty buffer");
    *loopback_bits.get_mut(0).unwrap() = input[0].is_some();
    // log::debug!("stateful_sink: input_bits: {:?}", input[0]);
    if let Some(input_bits) = input[0] {
        loopback_bits[1..].copy_from_bitslice(input_bits);
    }
    // log::debug!("stateful_sink: loopback after assign: {:?}", loopback_bits);
}

/**
 * Consumes one input, like sink, but no need to supply a loopback buffer.
 *
 * AKA /dev/null, trashcan
 */
pub fn sink(loopback: LoopbackRef, input: &[InputFrameRef], output: &mut [OutputFrameRef]) {
    assert_eq!(input.len(), 1);
    assert_eq!(output.len(), 0);
    assert!(
        loopback.is_none(),
        "sink should not have loopback state; see stateful_sink"
    );
}

fn concat_bitslices(left: &BitSlice, right: &BitSlice) -> BitBox {
    let mut bv = bitvec![];
    bv.extend_from_bitslice(left);
    bv.extend_from_bitslice(right);
    bv.into_boxed_bitslice()
}

pub fn prefix_bitslice(prefix: bool, slice: &BitSlice) -> BitBox {
    let mut prefix_vec = bitvec![0; 1];
    *prefix_vec.get_mut(0).unwrap() = prefix;
    concat_bitslices(prefix_vec.as_bitslice(), slice)
}

pub fn zero_bits(n: usize) -> BitBox {
    let mut bv = bitvec![];
    bv.resize(n, false);
    bv.into_boxed_bitslice()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calendar::APPLICATION_NODE;
    use crate::ports::{FrameSize, PortLabel, PortProperties, RttiType};
    use crate::scheduler::AllocationPolicy;
    use crate::scheduler::MappingConfiguration1x1;
    use crate::sim::SystemSimulationCallbacks;
    use crate::specs::{ApplicationNode, StatefulNode};
    use crate::NodeSpec;
    use bits::Bits;
    use petgraph::prelude::*;
    use sim::Inspect;

    const N_NODES: usize = 10;
    const N_CYCLES: usize = 10;
    type DType = u8;
    const DATA_SIZE: usize = <DType as bits::Bits>::SIZE;
    const N_DATA_SIZE: usize = <[Option<DType>; N_NODES] as bits::Bits>::SIZE;

    fn inspect_fanin_validate(app_spec: &Application) {
        let sink_id = NodeIndex::new(1);
        let sink_node = app_spec.get_node(sink_id);
        assert_eq!(sink_node.borrow().name(), "sink");
        (0..N_NODES).for_each(|i| {
            assert_eq!(
                sink_node.borrow().persistent_state().unwrap().as_bitslice()[0],
                true
            );
            let start_bit = 1 + i * (DATA_SIZE + 1);
            let end_bit = (i + 1) * (DATA_SIZE + 1);
            let state = DType::unpack(
                &sink_node.borrow().persistent_state().unwrap().as_bitslice()[start_bit..end_bit],
            );
            if i != N_NODES / 2 {
                assert_eq!(state, i as DType);
            } else {
                assert_eq!(state, 0 as DType);
            }
        });
    }

    fn inspect_fanin_sw<SIM: SystemSimulationTrait<{ APPLICATION_NODE }>>(
        cycle: usize,
        _sim: &SIM,
        app_spec: &Application,
    ) {
        // latency to reach the sink node
        let cycle_threshold = 3;
        if cycle > cycle_threshold {
            inspect_fanin_validate(app_spec);
        }
    }

    fn inspect_fanin_hw<SIM: SystemSimulationTrait<{ BUFFERING_DOUBLE }>>(
        metacycle: usize,
        _cycle: usize,
        _sim: &SIM,
        app_spec: &Application,
        _system_spec: &HardwareSpec,
    ) {
        // latency to reach the sink node
        let cycle_threshold = 2 * 3;
        if metacycle > cycle_threshold {
            inspect_fanin_validate(app_spec);
        }
    }

    fn build_fanin_app() -> Application {
        /*
                         id         +------\
        input_nodes[0] -----------> |       \
        input_nodes[1] -----------> |        |    +------+
        ...               0         | fan_in | => | sink |
        input_nodes[5] -----------> |        |    +------+
        input_nodes[N_NODES-1] ---> |       /
                                    +------/
        */

        let mut app_spec = Application::new();
        let fan_in = app_spec.add_node(Service::new(
            "fan_in",
            fan_in::<DType, [Option<DType>; N_NODES], N_NODES>,
            None,
            FrequencyFactor(1),
        ));
        let sink = app_spec.add_node(Service::new(
            "sink",
            stateful_sink,
            Some(zero_bits(N_DATA_SIZE + 1)),
            FrequencyFactor(1),
        ));
        let fan_in_ports = vec![
            (
                PortLabel::from(("input", N_NODES)),
                PortProperties {
                    direction: Direction::Incoming,
                    frame_size: FrameSize::Computed(RttiType::new::<DType>()),
                    framing_lead: FramingLead::Src,
                    ..PortProperties::default()
                },
            ),
            (
                PortLabel::from("output"),
                PortProperties {
                    direction: Direction::Outgoing,
                    frame_size: FrameSize::Computed(RttiType::new::<[Option<DType>; N_NODES]>()),
                    framing_lead: FramingLead::Src,
                    ..PortProperties::default()
                },
            ),
        ];
        app_spec
            .get_node(fan_in)
            .borrow_mut()
            .set_ports_properties(&fan_in_ports);

        let sink_ports = vec![(
            PortLabel::from("input"),
            PortProperties {
                direction: Direction::Incoming,
                frame_size: FrameSize::Computed(RttiType::new::<[Option<DType>; N_NODES]>()),
                ..PortProperties::default()
            },
        )];
        app_spec
            .get_node(sink)
            .borrow_mut()
            .set_ports_properties(&sink_ports);

        let link = Connection::new(
            app_spec
                .get_node(fan_in)
                .borrow()
                .get_port(&"output".into())
                .unwrap(),
            app_spec
                .get_node(sink)
                .borrow()
                .get_port(&"input".into())
                .unwrap(),
        );
        // TODO(cascaval): remove lead from here.
        app_spec.link_simplex_framing(fan_in, sink, link, FramingLead::Src);

        let source_ports = vec![(
            PortLabel::from("output"),
            PortProperties {
                direction: Direction::Outgoing,
                frame_size: FrameSize::Computed(RttiType::new::<DType>()),
                ..PortProperties::default()
            },
        )];
        let input_nodes = (0..N_NODES)
            .map(|n| {
                let input_state = if n != N_NODES / 2 {
                    prefix_bitslice(true, (n as DType).pack().as_bitslice())
                } else {
                    zero_bits(DATA_SIZE + 1)
                };
                let node = app_spec.add_node(Service::new(
                    format!("source {}", n).as_str(),
                    source,
                    Some(input_state),
                    FrequencyFactor(1),
                ));
                app_spec
                    .get_node(node)
                    .borrow_mut()
                    .set_ports_properties(&source_ports);
                node
            })
            .collect::<Vec<NodeIndex>>();
        log::debug!("sink node: {:?}", sink);
        input_nodes.iter().enumerate().for_each(|(node_i, node)| {
            let linkspec = Connection::new(
                app_spec
                    .get_node(*node)
                    .borrow()
                    .get_port(&"output".into())
                    .unwrap(),
                app_spec
                    .get_node(fan_in)
                    .borrow()
                    .get_port(&("input", node_i).into())
                    .unwrap(),
            );
            app_spec.link_simplex_framing(*node, fan_in, linkspec, FramingLead::Src);
        });
        log::debug!("app_spec:\n{}", app_spec);
        app_spec
    }

    #[test]
    fn test_fanin_app() {
        let _logger = env_logger::builder().is_test(true).try_init();

        let mut app_spec = build_fanin_app();

        // and now just simulate the app by itself
        let mut simulation = sim::SoftwareSystemSimulation::new(&mut app_spec);
        for cycle in 0..N_CYCLES {
            log::debug!("cycle: {}", cycle);
            simulation.simulate_system_one_cycle(
                &mut app_spec,
                &mut SystemSimulationCallbacks::default(),
            );
            let _cycle = 0;
            inspect_fanin_sw(cycle, &simulation, &app_spec);
        }
    }

    #[test]
    fn test_fanin_sys() {
        let _logger = env_logger::builder().is_test(true).try_init();

        let app_spec = build_fanin_app();
        let allocation_policy = AllocationPolicy::OneToOne(MappingConfiguration1x1::default());
        simulate_bittide_app(
            &app_spec,
            Some(Inspect::HW(inspect_fanin_hw)),
            2 * N_CYCLES,
            allocation_policy,
            &mut SystemSimulationCallbacks::default(),
            FailureProperties::default(),
        )
        .expect("Failed simulation");
    }

    const USIZE_SIZE: usize = <u64 as bits::Bits>::SIZE;
    const N_USIZE_SIZE: usize = <[Option<u64>; N_NODES] as bits::Bits>::SIZE;

    fn build_faninout_app() -> Application {
        /*
                                    +------\       /------+
        input_nodes[0] -----------> |       \     /       | --> output_nodes[0]
        input_nodes[1] -----------> |        |    |       | --> output_nodes[1]
        ...                         | fan_in | => | fan_out | ...
        input_nodes[N_NODES-1] ---> |       /     \       | --> output_nodes[N_NODES-1]
                                    +------/       \------+
        */

        let mut app_spec = Application::new();

        let fan_in = app_spec.add_node(Service::new(
            "fan_in",
            fan_in::<u64, [Option<u64>; N_NODES], N_NODES>,
            None,
            FrequencyFactor(1),
        ));
        let fan_out = app_spec.add_node(Service::new(
            "fan_out",
            fan_out::<u64, [Option<u64>; N_NODES], N_NODES>,
            None,
            FrequencyFactor(1),
        ));
        let link = Connection::new_for_testing(0, 0, N_USIZE_SIZE);
        app_spec.link_simplex_framing(fan_in, fan_out, link, FramingLead::Src);

        let mut fan_in_port_properties = (0..N_NODES)
            .map(|i| {
                (
                    PortLabel::Number(i),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(USIZE_SIZE),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                )
            })
            .collect::<Vec<_>>();
        fan_in_port_properties.push((
            PortLabel::Number(N_NODES + 1),
            PortProperties {
                frame_size: crate::FrameSize::Number(N_USIZE_SIZE),
                direction: Direction::Outgoing,
                ..Default::default()
            },
        ));
        app_spec
            .get_node(fan_in)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&fan_in_port_properties);

        let mut fan_out_port_properties = (0..N_NODES)
            .map(|i| {
                (
                    PortLabel::Number(i),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(USIZE_SIZE),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                )
            })
            .collect::<Vec<_>>();
        fan_out_port_properties.push((
            PortLabel::Number(N_NODES + 1),
            PortProperties {
                frame_size: crate::FrameSize::Number(N_USIZE_SIZE),
                direction: Direction::Incoming,
                ..Default::default()
            },
        ));
        app_spec
            .get_node(fan_out)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&fan_out_port_properties);

        let _input_nodes = (0..N_NODES)
            .map(|n| {
                let input_state = if n % 2 == 0 {
                    prefix_bitslice(true, ((n * n) as u64).pack().as_bitslice())
                } else {
                    zero_bits(USIZE_SIZE + 1)
                };
                let s = app_spec.add_node(Service::new(
                    format!("source {}", n).as_str(),
                    source,
                    Some(input_state),
                    FrequencyFactor(1),
                ));
                let linkspec = Connection::new_for_testing(0, n, USIZE_SIZE);
                app_spec.link_simplex_framing(s, fan_in, linkspec, FramingLead::Src);
                app_spec
                    .get_node(s)
                    .as_ref()
                    .borrow_mut()
                    .set_ports_properties(&[(
                        PortLabel::Number(0),
                        PortProperties {
                            frame_size: crate::FrameSize::Number(USIZE_SIZE),
                            direction: Direction::Outgoing,
                            ..Default::default()
                        },
                    )]);
                s
            })
            .collect::<Vec<NodeIndex>>();

        let _output_nodes = (0..N_NODES)
            .map(|n| {
                let output_state = zero_bits(USIZE_SIZE + 1);
                let s = app_spec.add_node(Service::new(
                    format!("sink {}", n).as_str(),
                    stateful_sink,
                    Some(output_state),
                    FrequencyFactor(1),
                ));
                let linkspec = Connection::new_for_testing(n, 0, USIZE_SIZE);
                app_spec.link_simplex_framing(fan_out, s, linkspec, FramingLead::Src);
                app_spec
                    .get_node(s)
                    .as_ref()
                    .borrow_mut()
                    .set_ports_properties(&[(
                        PortLabel::Number(0),
                        PortProperties {
                            frame_size: crate::FrameSize::Number(USIZE_SIZE),
                            direction: Direction::Incoming,
                            ..Default::default()
                        },
                    )]);
                s
            })
            .collect::<Vec<NodeIndex>>();

        log::debug!("app_spec:\n{}", app_spec);
        app_spec
    }

    fn inspect_faninout_check(app_spec: &Application) {
        (0..N_NODES).for_each(|i| {
            let node = app_spec.get_node_by_name(&format!("sink {}", i));
            if i % 2 == 0 {
                assert_eq!(
                    node.borrow().persistent_state().unwrap().as_bitslice()[0],
                    true
                );
                let state =
                    u64::unpack(&node.borrow().persistent_state().unwrap().as_bitslice()[1..]);
                assert_eq!(state, (i * i) as u64);
            } else {
                assert_eq!(
                    node.borrow().persistent_state().unwrap().as_bitslice()[1],
                    false
                );
            }
        });
    }

    fn inspect_faninout_hw<SIM: SystemSimulationTrait<{ BUFFERING_DOUBLE }>>(
        metacycle: usize,
        _cycle: usize,
        _sim: &SIM,
        app_spec: &Application,
        _system_spec: &HardwareSpec,
    ) {
        let cycle_threshold = 3 * 2;
        if metacycle > cycle_threshold {
            inspect_faninout_check(app_spec);
        }
    }

    fn inspect_faninout_app<SIM: SystemSimulationTrait<{ APPLICATION_NODE }>>(
        cycle: usize,
        _sim: &SIM,
        app_spec: &Application,
    ) {
        let cycle_threshold = 3;
        if cycle > cycle_threshold {
            inspect_faninout_check(app_spec);
        }
    }

    #[test]
    fn test_fan_inout_app() {
        let _logger = env_logger::builder().is_test(true).try_init();
        let mut app_spec = build_faninout_app();
        let mut simulation = sim::SoftwareSystemSimulation::new(&mut app_spec);

        for cycle in 0..N_CYCLES {
            simulation.simulate_system_one_cycle(
                &mut app_spec,
                &mut SystemSimulationCallbacks::default(),
            );
            inspect_faninout_app(cycle, &simulation, &app_spec);
        }
    }

    #[test]
    fn test_fan_inout_sys() {
        let _logger = env_logger::builder().is_test(true).try_init();
        let app_spec = build_faninout_app();
        let allocation_policy = AllocationPolicy::OneToOne(MappingConfiguration1x1::default());
        let system_spec = generate_system_spec(&app_spec, &allocation_policy);
        simulate_bittide(
            &system_spec,
            &[&app_spec],
            allocation_policy,
            Some(Inspect::HW(inspect_faninout_hw)),
            2 * N_CYCLES,
            &mut SystemSimulationCallbacks::default(),
            FailureProperties::default(),
        )
        .expect("Failed simulation");
    }
}
