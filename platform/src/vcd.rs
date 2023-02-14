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

use crate::calendar::Buffering;
use crate::DataWithValidity;
use crate::HardwareSpecType;
use crate::InputFrameRef;
use bitvec::prelude::*;
use chrono;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Display;
use std::fs;
use std::io;
use std::path;
use std::rc::Rc;
use vcd;

const DEFAULT_VCD_FILE: &str = "aegir.vcd";
pub const DEFAULT_TOP_MODULE: &str = "system_spec";
const DEFAULT_VCD_HEADER: &str = "aegir VCD";

#[derive(Clone, PartialEq)]
enum SizedData {
    Filled(BitBox<usize, Lsb0>),
    Undefined(usize),
}
#[derive(PartialEq)]
pub enum ChangeValue {
    Immediately,
    Defer,
}

pub struct VcdWriter {
    writer: vcd::Writer<fs::File>,
    is_error_state: bool,
    scope_stack: Vec<String>,
    id_map: HashMap<String, vcd::IdCode>,
    last_value_map: HashMap<vcd::IdCode, SizedData>,
    deferred_changes: HashMap<vcd::IdCode, SizedData>,
    timestamp: u64,
}

pub struct VcdTraceScope {
    writer: Rc<RefCell<VcdWriter>>,
    scope: String,
}

impl Drop for VcdTraceScope {
    fn drop(&mut self) {
        self.writer.borrow_mut().leave_scope(self.scope.as_str());
    }
}
pub struct VcdDeclScope {
    writer: Rc<RefCell<VcdWriter>>,
    scope: String,
}

impl Drop for VcdDeclScope {
    fn drop(&mut self) {
        self.writer.borrow_mut().upscope(self.scope.as_str());
    }
}

// TODO(pouyad) Add options to filter which signals will be traced.
impl VcdWriter {
    fn vcd_error_handler(&mut self, err: io::Error) {
        if !self.is_error_state {
            self.is_error_state = true;
            log::error!("VCD writing failed with error {:?}", err)
        }
    }

    pub fn managed_decl_scope<T>(writer: Rc<RefCell<VcdWriter>>, scope: &T) -> VcdDeclScope
    where
        T: Display + ?Sized,
    {
        writer.borrow_mut().add_module(scope);
        VcdDeclScope {
            writer: Rc::clone(&writer),
            scope: scope.to_string(),
        }
    }

    pub fn managed_trace_scope<T>(writer: Rc<RefCell<VcdWriter>>, scope: &T) -> VcdTraceScope
    where
        T: Display + ?Sized,
    {
        writer.borrow_mut().enter_scope(scope);
        VcdTraceScope {
            writer: Rc::clone(&writer),
            scope: scope.to_string(),
        }
    }

    pub fn write_header<const BUFFERING: Buffering>(
        writer: Rc<RefCell<Self>>,
        system_spec: &HardwareSpecType<BUFFERING>,
    ) {
        writer
            .borrow_mut()
            .writer
            .comment(DEFAULT_VCD_HEADER)
            .unwrap_or_else(|err| writer.borrow_mut().vcd_error_handler(err));
        writer
            .borrow_mut()
            .writer
            .date(chrono::Utc::now().to_string().as_str())
            .unwrap_or_else(|err| writer.borrow_mut().vcd_error_handler(err));
        {
            let _vcd_decl_scope =
                VcdWriter::managed_decl_scope(Rc::clone(&writer), DEFAULT_TOP_MODULE);
            writer.borrow_mut().add_integer_var::<u64>("sim_cycles");
            for node_index in system_spec.iter_nodes() {
                system_spec
                    .get_node(node_index)
                    .borrow_mut()
                    .vcd_write_scope(Rc::clone(&writer));
            }
        }
        writer
            .borrow_mut()
            .writer
            .enddefinitions()
            .unwrap_or_else(|err| writer.borrow_mut().vcd_error_handler(err));
        {
            let _vcd_trace_scope =
                VcdWriter::managed_trace_scope(Rc::clone(&writer), DEFAULT_TOP_MODULE);
            writer.borrow_mut().enter_cycle();
            writer
                .borrow_mut()
                .change_vector_immediately("sim_cycles", 0u64);
            for node_index in system_spec.iter_nodes() {
                system_spec
                    .get_node(node_index)
                    .borrow_mut()
                    .vcd_init(Rc::clone(&writer));
            }
            writer.borrow_mut().end_cycle();
        }
    }

    fn enter_scope<T: Display + ?Sized>(&mut self, name: &T) {
        self.scope_stack.push(name.to_string())
    }

    fn record_change(&mut self, id_code: vcd::IdCode, sized_data: &SizedData) {
        if self.is_error_state {
            return;
        }
        self._record_change(id_code, sized_data)
            .unwrap_or_else(|err| self.vcd_error_handler(err));
    }

    fn _record_change(&mut self, id_code: vcd::IdCode, sized_data: &SizedData) -> io::Result<()> {
        if let Some(last_sized_data) = self.last_value_map.get(&id_code) {
            if last_sized_data == sized_data {
                return Ok(());
            }
        }
        match sized_data {
            SizedData::Filled(data) => self.writer.change_vector(
                id_code,
                data.iter()
                    .rev()
                    .map(|b| (*b).into())
                    .collect::<Vec<_>>()
                    .as_slice(),
            )?,
            SizedData::Undefined(size) => self.writer.change_vector(
                id_code,
                (0..*size)
                    .map(|_| vcd::Value::X)
                    .collect::<Vec<_>>()
                    .as_slice(),
            )?,
        };
        self.last_value_map.insert(id_code, sized_data.clone());
        Ok(())
    }

    pub fn change_vector<V: bits::Bits + std::fmt::Debug>(&mut self, name: &str, v: V) {
        let v_bits = V::pack(&v).into_boxed_bitslice();
        if let Some(id_code) = self.lookup_id_code(&name.to_string()) {
            if cfg!(feature = "trace-echo-vcd-signal-changes") {
                log::trace!("VCD changing {}", self.scoped_name(name));
            }
            self.deferred_changes
                .insert(id_code, SizedData::Filled(v_bits));
        }
    }

    pub fn flush_after_simulation(&mut self) {
        self.enter_cycle();
        self.end_cycle();
    }

    pub fn change_vector_immediately<V: bits::Bits + std::fmt::Debug>(&mut self, name: &str, v: V) {
        let v_bits = V::pack(&v).into_boxed_bitslice();
        if let Some(id_code) = self.lookup_id_code(&name.to_string()) {
            if cfg!(feature = "trace-echo-vcd-signal-changes") {
                log::trace!("VCD changing {}", self.scoped_name(name));
            }
            self.record_change(id_code, &SizedData::Filled(v_bits));
        }
    }

    fn lookup_id_code(&self, name: &str) -> Option<vcd::IdCode> {
        let scoped_name = self.scoped_name(name);
        if let Some(id_code) = self.id_map.get(scoped_name.as_str()) {
            Some(*id_code)
        } else {
            log::warn!(
                "No such scoped name {} was defined for VCD dumps.",
                scoped_name
            );
            None
        }
    }

    pub fn change_input_frame_ref(
        &mut self,
        name: &str,
        frame_ref: InputFrameRef,
        frame_size: usize,
        change_value: ChangeValue,
    ) {
        if let Some(id_code) = self.lookup_id_code(&name.to_string()) {
            if cfg!(feature = "trace-echo-vcd-signal-changes") {
                log::trace!("VCD changing {}", self.scoped_name(name));
            }
            let sized_data = match frame_ref {
                Some(payload) => SizedData::Filled(payload.clone()),
                None => SizedData::Undefined(frame_size),
            };
            if change_value == ChangeValue::Defer {
                self.deferred_changes.insert(id_code, sized_data);
            } else {
                self.record_change(id_code, &sized_data);
            }
        }
    }

    pub fn change_output_frame_ref(
        &mut self,
        name: &str,
        output_frame_ref: &DataWithValidity,
        frame_size: usize,
        change_value: ChangeValue,
    ) {
        self.change_input_frame_ref(
            name,
            if output_frame_ref.valid {
                Some(&output_frame_ref.data)
            } else {
                None
            },
            frame_size,
            change_value,
        );
    }

    pub fn enter_cycle(&mut self) {
        if self.is_error_state {
            return;
        }
        self._enter_cycle()
            .unwrap_or_else(|err| self.vcd_error_handler(err));
    }

    fn _enter_cycle(&mut self) -> io::Result<()> {
        // Start new cycle.
        self.writer.timestamp(self.timestamp)?;
        // Write all deferred changes; these should appear in the new cycle which we've begun.
        let deferred_changes: HashMap<vcd::IdCode, SizedData> =
            self.deferred_changes.drain().collect();
        for (id_code, data) in deferred_changes {
            self._record_change(id_code, &data)?;
        }
        Ok(())
    }

    pub fn end_cycle(&mut self) {
        if self.is_error_state {
            return;
        }
        self._end_cycle()
            .unwrap_or_else(|err| self.vcd_error_handler(err));
    }

    fn _end_cycle(&mut self) -> io::Result<()> {
        self.writer.end()?;
        self.timestamp += 1;
        Ok(())
    }

    fn leave_scope<T: Display + ?Sized>(&mut self, scope: &T) {
        let popped_scope = self
            .scope_stack
            .pop()
            .expect("Attempted to leave a scope without entering one first.");
        assert_eq!(popped_scope, scope.to_string());
    }

    fn add_module<T: Display + ?Sized>(&mut self, name: &T) {
        if self.is_error_state {
            return;
        }
        self._add_module::<T>(name)
            .unwrap_or_else(|err| self.vcd_error_handler(err));
    }

    fn _add_module<T: Display + ?Sized>(&mut self, name: &T) -> io::Result<()> {
        self.writer.add_module(&name.to_string())?;
        self.scope_stack.push(name.to_string());
        Ok(())
    }

    fn upscope<T: Display + ?Sized>(&mut self, scope: &T) {
        if self.is_error_state {
            return;
        }
        self._upscope::<T>(scope)
            .unwrap_or_else(|err| self.vcd_error_handler(err));
    }

    fn _upscope<T: Display + ?Sized>(&mut self, scope: &T) -> io::Result<()> {
        self.leave_scope(scope);
        self.writer.upscope()
    }

    pub fn add_integer_var<T: Sized>(&mut self, reference: &str) {
        if self.is_error_state {
            return;
        }
        self._add_integer_var::<T>(reference)
            .unwrap_or_else(|err| self.vcd_error_handler(err));
    }

    fn _add_integer_var<T: Sized>(&mut self, reference: &str) -> io::Result<()> {
        let var_id = self.writer.add_var(
            vcd::VarType::Integer,
            std::mem::size_of::<T>() as u32 * 8,
            &reference.to_string(),
            None,
        )?;
        self.add_id_map(&reference.to_string(), var_id);
        Ok(())
    }

    pub fn add_var(
        &mut self,
        var_type: vcd::VarType,
        width: usize,
        reference: &str,
        index: Option<vcd::ReferenceIndex>,
    ) {
        if self.is_error_state {
            return;
        }
        self._add_var(var_type, width, reference, index)
            .unwrap_or_else(|err| self.vcd_error_handler(err));
    }

    fn _add_var(
        &mut self,
        var_type: vcd::VarType,
        width: usize,
        reference: &str,
        index: Option<vcd::ReferenceIndex>,
    ) -> io::Result<()> {
        let var_id = self
            .writer
            .add_var(var_type, width as u32, &reference.to_string(), index)?;
        self.add_id_map(&reference.to_string(), var_id);
        Ok(())
    }

    fn scoped_name(&self, name: &str) -> String {
        self.scope_stack.join(".") + "." + name
    }

    fn add_id_map(&mut self, name: &str, vcd_id: vcd::IdCode) {
        let scoped_name = self.scoped_name(name);
        if self.id_map.contains_key(scoped_name.as_str()) {
            log::warn!(
                "Scoped name {} is was redefined for VCD dumps.",
                scoped_name
            );
        }
        self.id_map.insert(scoped_name, vcd_id);
    }

    // TODO(pouyad) add plumping to specify different vcd paths.
    #[allow(dead_code)]
    fn new(dst: path::PathBuf) -> io::Result<Self> {
        let dst_file = fs::File::create(dst)?;
        Ok(Self {
            writer: vcd::Writer::new(dst_file),
            ..Default::default()
        })
    }
}

impl Default for VcdWriter {
    fn default() -> Self {
        let mut vcd_path = path::PathBuf::from(std::env::temp_dir());
        vcd_path.push(DEFAULT_VCD_FILE);
        let vcd_file = fs::File::create(&vcd_path).expect(&format!(
            "Failed to create default VCD file {:?}.",
            vcd_path
        ));
        log::debug!("VCD file: {}", vcd_path.to_str().unwrap());
        Self {
            is_error_state: false,
            writer: vcd::Writer::new(vcd_file),
            scope_stack: vec![],
            id_map: HashMap::new(),
            timestamp: 0,
            deferred_changes: HashMap::new(),
            last_value_map: HashMap::new(),
        }
    }
}

/// An object implementing the VcdComponent can declare and initialize values to
/// be traced by a VCD. Each such object is responsible for calling their inner
/// VcdComponent objects.
///
/// Example:
/// struct B { b: u32}
/// struct A { a: B, x: u32 }
///
/// impl VcdComponent for B {
///     fn vcd_write_scope(&self, writer: Rc<RefCell<VcdWriter>>) {
///         let _vcd_A_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), "B");
///         writer.borrow_mut().add_integer_var::<u32>("b");
///     }
///     fn vcd_init(&self, writer: Rc<RefCell<VcdWriter>>) {
///         let _vcd_A_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), "B");
///          writer.borrow_mut().change_vector_immediately("b", 0);
///     }
/// }
///
/// impl VcdComponent for A {
///     fn vcd_write_scope(&self, writer: Rc<RefCell<VcdWriter>>) {
///         let _vcd_A_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), "A");
///         self.vcd_write_scope(Rc::clone(&writer));
///         writer.borrow_mut().add_integer_var::<u32>("x");
///     }
///     fn vcd_init(&self, writer: Rc<RefCell<VcdWriter>>) {
///         let _vcd_A_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), "A");
///         self.vcd_init(Rc::clone(&writer));
///         writer.borrow_mut().change_vector_immediately("x", 1);
///     }
/// }
///
/// // For illustrating this example only; actual usage is through sim::SystemSimulationCallbacks.
/// writer = Rc::new(RefCell::new(VcdWriter::default()));
/// VcdWriter::write_header(writer);
///
/// This code introduces signals "A.B.b", and "A.x" into the VCD. It also sets
/// their values to b = 0, and x = 1 at simulation time 0, i.e., before the
/// simulator has stepped.
pub trait VcdComponent {
    /// A VCD header contains a hierarchical scope of names to be traced. Each
    /// component is expect to declare its variables to be traced and call
    /// `vcd_write_scope` on its members implementing the `VcdComponent`
    /// trait.
    fn vcd_write_scope(&self, vcd_writer: Rc<RefCell<VcdWriter>>);

    /// Components can record the initial value of their values to be traced.
    /// Components should call `vcd_init` on members implementing the
    /// `VcdComponent` trait.
    fn vcd_init(&self, vcd_writer: Rc<RefCell<VcdWriter>>);
}
