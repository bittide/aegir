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

//! A bittide system consists of a number of ComputeNodes and Switches.
//!
//! The nodes and switches are connected according to a SystemSpec.

use bitvec::prelude::BitVec;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;
use std::rc::Rc;

use super::*;
use crate::app::Service;
use crate::app::ServiceHandle;
use crate::calendar::Buffering;
use crate::calendar::IOCalendarVariant;
use crate::calendar::NodeCalendar;
use crate::hw::config::NodeConfiguration;
use crate::hw::gather::GatherEngine;
use crate::hw::scatter::ScatterEngine;
use crate::hw::RunConfig;
use crate::mailbox::MailBox;
use crate::sim::OptionSimCallbacks;
use crate::specs::LinkProperties;
use crate::specs::{
    ApplicationNode, Frequency, ProvisionedComputeNode, ProvisionedNode, StatefulNode,
};
use crate::vcd::{ChangeValue, VcdComponent, VcdWriter};
use crate::NodeSpec;
use ::vcd as vcd_ext;

pub type HostAddressType = u64;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HostAddress(HostAddressType);

#[derive(Clone, Debug)]
pub struct HostAddressRange {
    pub start: HostAddressType,
    pub end: HostAddressType,
}

impl HostAddressRange {
    pub fn new(start: HostAddress, end: HostAddress) -> Self {
        HostAddressRange {
            start: start.0,
            end: end.0,
        }
    }

    pub fn size(&self) -> usize {
        (self.start.max(self.end) - self.start.min(self.end)) as usize
    }
}

impl Default for HostAddressRange {
    fn default() -> Self {
        Self { start: 0, end: 0 }
    }
}

const HOST_MEMORY_MAILBOX_SIZE: usize = 0x00ffffff;

#[derive(Clone, Debug)]
enum ActiveWriteBuffer {
    WriteBuffer0,
    WriteBuffer1,
}

impl ActiveWriteBuffer {
    fn toggle(&self) -> Self {
        match self {
            Self::WriteBuffer0 => Self::WriteBuffer1,
            Self::WriteBuffer1 => Self::WriteBuffer0,
        }
    }
}

impl Default for ActiveWriteBuffer {
    fn default() -> Self {
        ActiveWriteBuffer::WriteBuffer0
    }
}

// The values of these mappings are hypothetical for the time being.
#[derive(Clone, Debug)]
pub struct HostMemoryCfg<const BUFFERING: Buffering> {
    mailboxes: [[HostAddressRange; BUFFERING]; BUFFERING],
    /// Word size of the memory, in bits.
    word_size: usize,
    // Size of the memory in words.
    memory_size: usize,
    run_config: RunConfig,
    write_buffer: ActiveWriteBuffer,
    metacycle: usize, // Can be implemented by a single bit, but this is more readable.
}

/// Mailboxes are managed by means of address ranges in different buffering
/// scenarios.
///
/// Double Buffering
///
/// When double-buffering, mutually exclusive regions of memory are designated
/// for inboxes/outboxes. Because data produced in metacycle M(i) won't be
/// consumed until metacycle M(i+2) there exists 2 mailbox memory regions per
/// metacycle.
///
///```text
/// metacycle(M(k)-parity, buffer) | M(i)     M(i+1)    M(i+2)    M(i+3)
/// -------------------------------+-----------------------------------
/// mailboxes(0,0)                 |  W         -          R        -
/// mailboxes(0,1)                 |  R         -          W        -
/// mailboxes(1,0)                 |  -         W          -        R
/// mailboxes(1,1)                 |  -         R          -        W
///```
/// action:
///   - : no-op (preserve mailbox data)
///   W : writes into the mailbox base addresses
///   R : reads from the mailbox base addresses
///
///
/// Single Buffering
///
/// With single buffered memories, data dependencies are managed by the
/// scheduler without HW enforced memory isolation.
///
/// TODO(pouyad): implement these semantics.
impl<const BUFFERING: Buffering> HostMemoryCfg<BUFFERING> {
    fn new(word_size: usize, memory_size: usize) -> Self {
        // The total number of memory words used for mailboxes, where each
        // mailbox has HOST_MEMORY_MAILBOX_SIZE words.
        let total_mailbox_memory = match BUFFERING {
            BUFFERING_SINGLE => HOST_MEMORY_MAILBOX_SIZE,
            BUFFERING_DOUBLE => 4 * HOST_MEMORY_MAILBOX_SIZE,
            _ => panic!("Invalid buffering configuration."),
        };
        //    0 +--------+
        //      |        |
        //      |        |  unreserved host memory address space
        //      |        |
        //      +--------+ (memory_size - total_mailbox_memory)
        //      |////////|
        //      |////////|  memory address space used for mailboxes
        //      |////////|
        //  END +--------+ (memory_size)
        //
        // The mailbox address space is where mailboxes are mapped in host memory.
        // Individual mailbox addresses are determined by Mailbox::materialize_addresses.
        //
        // A mailbox address is an offset into a mailbox region of memory.
        assert!(memory_size >= total_mailbox_memory);
        let mailbox_start_address = memory_size - total_mailbox_memory;
        let mut range = [0; BUFFERING];
        for i in 0..range.len() {
            range[i] = i;
        }
        Self {
            mailboxes: range.map(|parity| {
                range.map(|buffer| {
                    let start_address =
                        mailbox_start_address + (2 * parity + buffer) * HOST_MEMORY_MAILBOX_SIZE;
                    HostAddressRange::new(
                        HostAddress(start_address as HostAddressType),
                        HostAddress((start_address + HOST_MEMORY_MAILBOX_SIZE) as HostAddressType),
                    )
                })
            }),
            word_size,
            memory_size,
            run_config: RunConfig::default(),
            write_buffer: ActiveWriteBuffer::default(),
            metacycle: 0,
        }
    }

    pub fn word_size(&self) -> usize {
        self.word_size
    }

    pub fn memory_size(&self) -> usize {
        self.memory_size
    }
    pub fn out_mailbox(&self) -> &HostAddressRange {
        match BUFFERING {
            BUFFERING_SINGLE => &self.mailboxes[0][0],
            BUFFERING_DOUBLE => {
                let idx: usize = self.run_config.clone().into();
                &self.mailboxes[idx][self.write_buffer.clone() as usize]
            }
            _ => panic!("Invalid buffering configuration."),
        }
    }

    pub fn in_mailbox(&self) -> &HostAddressRange {
        match BUFFERING {
            BUFFERING_SINGLE => &self.mailboxes[0][0],
            BUFFERING_DOUBLE => {
                let idx: usize = self.run_config.clone().into();
                &self.mailboxes[idx][self.write_buffer.toggle() as usize]
            }
            _ => panic!("Invalid buffering configuration."),
        }
    }

    pub fn advance_metacycle(&mut self) {
        self.run_config = self.run_config.toggle();
        self.metacycle += 1;
        if self.metacycle % 2 == 0 {
            self.write_buffer = self.write_buffer.toggle();
        }
    }
}

#[derive(Clone, Debug)]
struct HostMemory<const BUFFERING: Buffering> {
    // TODO(pouyad): host memory is modeled as a flat physical address space; we
    // probably want some sort of virtual memory in the future.
    /// Host memory is represented as a hashmap because it's assumed to be sparsely
    /// modeled by aegir (vs aegir's modeling of IO memories).
    memory: HashMap<HostAddress, DataWithValidity>,
    pub cfg: HostMemoryCfg<BUFFERING>,
}

impl<const BUFFERING: Buffering> HostMemory<BUFFERING> {
    /// C'tor of host memory with specified `memory_size` in bytes.
    pub fn new(memory_size: usize) -> Self {
        Self {
            memory: HashMap::new(),
            cfg: HostMemoryCfg::new(8, memory_size), // Assume byte-width memory.
        }
    }

    /// return the slice of memory that is to be filled by the application.
    pub fn write(&mut self, address: &HostAddress) -> &mut DataWithValidity {
        assert!(address.0 < self.cfg.memory_size as HostAddressType);
        if !self.memory.contains_key(&address) {
            self.memory.insert(
                address.clone(),
                DataWithValidity {
                    data: BitVec::repeat(false, 8).into_boxed_bitslice(),
                    valid: false,
                },
            );
        }
        self.memory.get_mut(address).unwrap()
    }

    /// return the frame at the provided address
    pub fn read(&self, address: HostAddress) -> Option<&Data> {
        assert!(address.0 < self.cfg.memory_size as HostAddressType);
        if self.memory.contains_key(&address) && self.memory[&address].valid {
            Some(&self.memory[&address].data)
        } else {
            None
        }
    }

    pub fn advance_metacycle(&mut self) {
        self.cfg.advance_metacycle();
    }
}

/// Represents a physical bittide node
///
/// A compute node consists of:
///
///  - an execution engine/processing element (PE)
///
///  - local state:
///    - a cycle counter
///    - a set of (currently a single one) of application information:
///      - a reference to an app node (Service)
///
///  - for each of the links:
///    - the scatter/gather engines.
#[derive(Clone, Debug)]
pub struct ComputeNode<const BUFFERING: Buffering> {
    name: String,
    services: HashMap<ServiceHandle, Rc<RefCell<Service>>>,

    /// input links: scatter engines, one for each input link, indexed by `port`.
    scatterers: Vec<ScatterEngine<BUFFERING>>,

    /// output links: gather engines, one for each output link, indexed by `port`
    gatherers: Vec<GatherEngine<BUFFERING>>,

    /// boottime value: how many local cycles are in a metacycle.
    cycles_per_metacycle: [Cycle; BUFFERING],

    /// local cycle counter
    local_cycles: Cycle,

    /// initial clock counter
    /// by default nodes start with a random initial cycle value. This value
    /// together with local cycles, will be used to compute UGNs. The local
    /// cycle value is returned by the cycles method.
    starting_cycles: Cycle,

    // required by the NodeSpec trait
    frequency: Frequency,

    /// Mailboxes manage the lowering of service messages to HW IO. They're
    /// computed as a step of scheduling.
    mailbox: Option<MailBox>,

    /// Execution calendar of the node.
    node_calendar: [NodeCalendar; BUFFERING],
    run_config: RunConfig,
    run_entry: usize,
    run_cycles: usize,
    require_advance_metacycle: bool,

    host_memory: HostMemory<BUFFERING>,

    crashed: bool,
}

struct ComputeNodeSystemContext<'a, const BUFFERING: Buffering> {
    service_handle: ServiceHandle,
    node: &'a ComputeNode<BUFFERING>,
    app_name: &'a str,
}

impl<'a, const BUFFERING: Buffering> SystemContext for ComputeNodeSystemContext<'a, BUFFERING> {
    fn input_links(&self) -> Vec<LinkProperties> {
        self.node
            .mailbox
            .as_ref()
            .expect("Missing mailbox assignment.")
            .get_app_mailboxes(self.service_handle.app_id.clone(), self.app_name)
            .expect(format!("Could not find mailboxes for application {}", self.app_name).as_str())
            .inboxes
            .iter()
            .enumerate()
            .map(|(i, inbox)| {
                let scatter_index: usize = Port::new_in(
                    inbox
                        .mapped_endpoint
                        .as_ref()
                        .expect(
                            format!(
                                "Unmapped inbox for input {} of service {}",
                                i, self.app_name
                            )
                            .as_str(),
                        )
                        .hw_io_index
                        .expect("Uninitialized port mapping"),
                )
                .into();
                LinkProperties {
                    status: self.node.scatterers[scatter_index].get_link_status(),
                }
            })
            .collect::<Vec<_>>()
    }

    fn output_links(&self) -> Vec<LinkProperties> {
        self.node
            .mailbox
            .as_ref()
            .expect("Missing mailbox assignment.")
            .get_app_mailboxes(self.service_handle.app_id.clone(), self.app_name)
            .expect(format!("Could not find mailboxes for application {}", self.app_name).as_str())
            .outboxes
            .iter()
            .enumerate()
            .map(|(i, outbox)| {
                let gather_index: usize = Port::new_out(
                    outbox
                        .mapped_endpoint
                        .as_ref()
                        .expect(
                            format!(
                                "Unmapped outbox for output {} of service {}",
                                i, self.app_name
                            )
                            .as_str(),
                        )
                        .hw_io_index
                        .expect("Uninitialized port mapping"),
                )
                .into();
                LinkProperties {
                    status: self.node.gatherers[gather_index].get_link_status(),
                }
            })
            .collect::<Vec<_>>()
    }
}

impl<const BUFFERING: Buffering> NodeSpec<BUFFERING> for ComputeNode<BUFFERING> {
    fn step(
        &mut self,
        _inputs: &[InputFrameRef],
        _outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        let idx: usize = self.run_config.clone().into();
        if self.crashed {
            log::trace!(
                "Skipping step() for crashed compute node name: \"{}\" id: {}",
                self.name(),
                idx,
            );
            return Ok(());
        }
        if self.require_advance_metacycle {
            return Err(Error::OutOfCalendar);
        }
        let _vcd_node_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), self.name()));

        let node_calendar_len = self.node_calendar[idx].len();
        assert!(match BUFFERING {
            BUFFERING_SINGLE => self.run_config == RunConfig::default(),
            _ => true,
        });
        let node_calendar_entry = self.node_calendar[idx][self.run_entry].clone();

        // We run the service function on the last cycle of the duration.
        if node_calendar_entry.service_handle.is_some()
            && (self.run_cycles + 1) as u32 == node_calendar_entry.duration
        {
            let service_handle = node_calendar_entry.service_handle.as_ref().unwrap();
            assert!(self.services.contains_key(&service_handle));
            log::debug!(
                ">>> Computing {} local_cycle {} calendar_entry: {:?} run_cycles {}",
                self.name,
                self.local_cycles,
                node_calendar_entry,
                self.run_cycles
            );
            let app_name = self.services[&service_handle].borrow().name().to_string();
            let app_mailboxes = self
                .mailbox
                .as_ref()
                .expect(
                    format!("Missing mailbox assignment for compute node {}.", self.name).as_str(),
                )
                .get_app_mailboxes(service_handle.app_id.clone(), app_name.as_str())
                .expect(format!("Could not find mailboxes for application {}", app_name).as_str());
            log::trace!("mailboxes: {:#?}", app_mailboxes);
            if log::log_enabled!(log::Level::Debug) {
                for i in 0..self.scatterers.len() {
                    log::debug!("PE input {}[{}]", self.name(), i);
                    self.scatterers[i].debug_dump_memory();
                }
            }
            // call the application function through the service node
            let mut app_inputs: Vec<Data> = vec![];
            let mut app_inputs_ref = vec![];
            for i in 0..app_mailboxes.inboxes.len() {
                let data = BitVec::repeat(
                    false,
                    self.services[&service_handle]
                        .as_ref()
                        .borrow()
                        .get_msg_size(Port::new_in(i)),
                )
                .into_boxed_bitslice();
                app_inputs.push(data);
            }
            for (i, (data, inbox)) in app_inputs
                .iter_mut()
                .zip(app_mailboxes.inboxes.iter())
                .enumerate()
            {
                let inbox_mapping = inbox.mapped_endpoint.as_ref().expect(
                    format!("Unmapped inbox for input {} of service {}", i, app_name).as_str(),
                );
                let read_base_address = inbox_mapping
                    .base_address
                    .expect("Unmaterialized base address.");
                app_inputs_ref.push(match inbox_mapping.hw_io_index {
                    Some(hw_io_index) => {
                        self.read_input(Port::new_in(hw_io_index), read_base_address, data)
                    }
                    None => self.read_input_from_host(
                        HostAddress(read_base_address as HostAddressType),
                        data,
                    ),
                });
            }
            let app_inputs_ref = app_inputs_ref
                .iter()
                .map(|x| x.as_deref())
                .collect::<Vec<_>>();
            let mut app_outputs = (0..app_mailboxes.outboxes.len())
                .map(|i| DataWithValidity {
                    data: BitVec::repeat(
                        false,
                        self.services[&service_handle]
                            .borrow()
                            .get_msg_size(Port::new_out(i)),
                    )
                    .into_boxed_bitslice(),
                    valid: false,
                })
                .collect::<Vec<_>>();
            let mut app_outputs_ref = app_outputs.iter_mut().collect::<Vec<_>>();
            callbacks.vcd(|writer| {
                for (i, frame_ref) in app_inputs_ref.iter().enumerate() {
                    let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
                    let frame_size = self.services[&service_handle]
                        .borrow()
                        .get_msg_size(Port::new_in(i));
                    writer.borrow_mut().change_input_frame_ref(
                        "input",
                        *frame_ref,
                        frame_size,
                        vcd::ChangeValue::Immediately,
                    );
                }
            });
            for (i, contents) in app_inputs_ref.iter().enumerate() {
                if contents.is_some() {
                    log::trace!(
                        "inputs[{}] ({}): {}",
                        i,
                        self.services[&service_handle]
                            .borrow()
                            .get_msg_size(Port::new_in(i)),
                        contents
                            .unwrap()
                            .as_bitslice()
                            .iter()
                            .map(|b| (if *b { 1u32 } else { 0u32 }).to_string())
                            .collect::<String>(),
                    );
                }
            }
            {
                // block for VCD scope of service's state
                let _vcd_service_scope;
                if self.services[&service_handle]
                    .borrow()
                    .persistent_state()
                    .is_some()
                {
                    _vcd_service_scope = callbacks.get_vcd_writer().map(|writer| {
                        VcdWriter::managed_trace_scope(
                            Rc::clone(&writer),
                            format!("service_{}", service_handle).as_str(),
                        )
                    });
                }
                // While running the action function for this service node,
                // we install data at a known memory location to enable a
                // system call handler to service system calls.
                // This handler must have knowledge of which service function
                // is running, so that it can for example report the status
                // of the links providing input/output to the currently running
                // service function (i.e. map from function input number to
                // scatter unit, ignoring the links which other action functions
                // are using but the current one isn't).
                //
                // We simulate this, by passing a trait instance, which can
                // represents the handler, plus its knowledge of which action
                // function is currently running.
                let sys_call_ctx = ComputeNodeSystemContext {
                    service_handle: service_handle.clone(),
                    node: self,
                    app_name: &app_name,
                };
                self.services[&service_handle]
                    .borrow_mut()
                    .run_action_function(
                        app_inputs_ref.as_slice(),
                        &mut app_outputs_ref,
                        callbacks,
                        &sys_call_ctx,
                    )?;
            }
            callbacks.vcd(|writer| {
                for (i, frame_ref) in app_outputs_ref.iter().enumerate() {
                    let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
                    let frame_size = self.services[&service_handle]
                        .borrow()
                        .get_msg_size(Port::new_out(i));
                    writer.borrow_mut().change_output_frame_ref(
                        "output",
                        *frame_ref,
                        frame_size,
                        vcd::ChangeValue::Defer,
                    );
                }
            });

            for (i, contents) in app_outputs.iter().enumerate() {
                log::trace!(
                    "outputs[{}] ({}): {:?} {}",
                    i,
                    self.services[&service_handle]
                        .borrow()
                        .get_msg_size(Port::new_out(i)),
                    contents
                        .data
                        .to_bitvec()
                        .iter()
                        .map(|b| (if *b { 1u32 } else { 0u32 }).to_string())
                        .collect::<String>(),
                    contents.valid,
                );
            }
            for (i, (output, outbox)) in app_outputs
                .iter()
                .zip(app_mailboxes.outboxes.iter())
                .enumerate()
            {
                let outbox_mapping = outbox.mapped_endpoint.as_ref().expect(
                    format!("Unmapped outbox for output {} of service {}", i, app_name).as_str(),
                );
                let write_base_address = outbox_mapping
                    .base_address
                    .expect("Unmaterialized base address.");
                match outbox_mapping.hw_io_index {
                    Some(hw_io_index) => self.write_output(
                        Port::new_out(hw_io_index),
                        write_base_address,
                        &output,
                        callbacks,
                    ),
                    None => self.write_output_to_host(
                        HostAddress(write_base_address as HostAddressType),
                        output,
                    ),
                };
            }
            if log::log_enabled!(log::Level::Debug) {
                for i in 0..self.gatherers.len() {
                    log::debug!("PE output {}[{}]", self.name(), i);
                    self.gatherers[i].debug_dump_memory();
                }
            }
        }
        self.local_cycles += 1;
        (
            self.run_entry,
            self.run_cycles,
            self.require_advance_metacycle,
        ) = if self.run_cycles + 1 < node_calendar_entry.duration as usize {
            (self.run_entry, self.run_cycles + 1, false)
        } else {
            if self.run_entry + 1 < node_calendar_len {
                (self.run_entry + 1, 0, false)
            } else {
                (0, 0, true)
            }
        };
        callbacks.vcd(|writer| {
            writer
                .borrow_mut()
                .change_vector("metacycles", self.metacycle() as u32);
            writer
                .borrow_mut()
                .change_vector("local_cycles", self.local_cycles as u32);
            writer
                .borrow_mut()
                .change_vector("current_cycles", self.local_cycles() as u32);
        });

        log::debug!("<<< Computing {}", self.name);
        Ok(())
    }

    fn name(&self) -> &str {
        self.name.as_str()
    }

    fn set_port_framing(&mut self, _port: Port, _lead: FramingLead) {
        unimplemented!();
    }

    fn into_provisioned_node(&self) -> Option<&dyn ProvisionedNode<BUFFERING>> {
        Some(self)
    }

    fn into_mut_provisioned_node(&mut self) -> Option<&mut dyn ProvisionedNode<BUFFERING>> {
        Some(self)
    }

    fn into_provisioned_compute_node(&self) -> Option<&dyn ProvisionedComputeNode<BUFFERING>> {
        Some(self)
    }

    fn into_mut_provisioned_compute_node(
        &mut self,
    ) -> Option<&mut dyn ProvisionedComputeNode<BUFFERING>> {
        Some(self)
    }
}

impl<const BUFFERING: Buffering> ProvisionedNode<BUFFERING> for ComputeNode<BUFFERING> {
    fn cycles_per_metacycle(&self) -> [Cycle; BUFFERING] {
        self.cycles_per_metacycle
    }

    fn set_cycles_per_metacycle(&mut self, cpm: [Cycle; BUFFERING]) {
        self.cycles_per_metacycle = cpm;
    }

    fn metacycle(&self) -> Cycle {
        crate::hw::metacycle(self.local_cycles, self.cycles_per_metacycle)
    }

    fn get_scatter_memory_size(&self, port: Port) -> usize {
        let port_idx: usize = port.into();
        assert_eq!(port.direction(), Direction::Incoming);
        self.scatterers[port_idx].memory_size()
    }

    fn get_gather_memory_size(&self, port: Port) -> usize {
        let port_idx: usize = port.into();
        assert_eq!(port.direction(), Direction::Outgoing);
        self.gatherers[port_idx].memory_size()
    }

    fn set_scatter_memory_size(&mut self, port: Port, memory_size: usize) {
        let port_idx: usize = port.into();
        assert_eq!(port.direction(), Direction::Incoming);
        self.scatterers[port_idx].set_memory_size(memory_size);
    }

    fn set_gather_memory_size(&mut self, port: Port, memory_size: usize) {
        let port_idx: usize = port.into();
        assert_eq!(port.direction(), Direction::Outgoing);
        self.gatherers[port_idx].set_memory_size(memory_size);
    }

    fn set_scatter_link_status(&mut self, port: Port, link_status: LinkStatus) {
        let port_idx: usize = port.into();
        assert_eq!(port.direction(), Direction::Incoming);
        self.scatterers[port_idx].set_link_status(link_status);
    }

    fn set_gather_link_status(&mut self, port: Port, link_status: LinkStatus) {
        let port_idx: usize = port.into();
        assert_eq!(port.direction(), Direction::Outgoing);
        self.gatherers[port_idx].set_link_status(link_status);
    }

    fn register_app(&mut self, service_handle: ServiceHandle, service: Rc<RefCell<Service>>) {
        self.services.insert(service_handle, service);
    }

    fn set_calendar(&mut self, calendar_variant: CalendarVariant<BUFFERING>) {
        match &calendar_variant {
            CalendarVariant::Node(calendar) => {
                self.node_calendar = calendar.to_owned();
            }
            CalendarVariant::Crossbar(_) => {
                panic!("Illegal calendar assignment for compute node.")
            }
        }
    }

    fn set_io_calendar(&mut self, calendar_variant: IOCalendarVariant<BUFFERING>, port: Port) {
        match &calendar_variant {
            IOCalendarVariant::Input(_) => {
                let port_idx: usize = port.into();
                self.scatterers[port_idx].set_calendar(calendar_variant)
            }
            IOCalendarVariant::Output(_) => {
                let port_idx: usize = port.into();
                self.gatherers[port_idx].set_calendar(calendar_variant)
            }
        }
    }

    fn get_mailbox(&self) -> Option<&MailBox> {
        self.mailbox.as_ref()
    }

    fn set_mailbox(&mut self, mailbox: MailBox) {
        self.mailbox = Some(mailbox);
    }

    fn frequency(&self) -> Frequency {
        self.frequency
    }

    fn set_frequency(&mut self, freq: Frequency) {
        self.frequency = freq;
    }

    fn step_gather(
        &mut self,
        port: Port,
        outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        let _vcd_node_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), self.name()));

        // the application outputs are now layed out into tx memories. we need
        // to gather them and send on the wire, that is the "outputs" argument.

        let port_idx: usize = port.into();
        let _vcd_port_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), &port));
        for (idx, output) in outputs.iter_mut().enumerate() {
            self.gatherers[port_idx]
                .step(output, callbacks)
                .unwrap_or_else(|err| {
                    panic!(
                        "Node {} cycle {}: stepping gather of output {} failed on port {} with error {}",
                        self.name(),
                        self.local_cycles,
                        idx,
                        port,
                        err
                    )
                });
        }
        log::debug!("Node {} gather[{}]:", self.name(), port_idx);
        self.gatherers[port_idx].debug_dump_memory();

        Ok(())
    }

    fn step_scatter(
        &mut self,
        port: Port,
        inputs: &[InputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        let _vcd_node_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), self.name()));

        let port_idx: usize = port.into();
        for input in inputs.iter() {
            let _vcd_port_scope = callbacks
                .get_vcd_writer()
                .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), &port));
            self.scatterers[port_idx]
                .step(*input, callbacks)
                .unwrap_or_else(|_| {
                    panic!(
                        "cycle {}: Failed receiving on port {}",
                        self.local_cycles, port
                    )
                });
        }
        log::debug!("Node {} scatter[{}]:", self.name(), port_idx);
        self.scatterers[port_idx].debug_dump_memory();
        Ok(())
    }

    /// bookkeeping for advancing a node to the next metacycle.
    ///
    /// This includes, resetting the calendars and the read/write pointers
    /// into memory, and resetting the local local_cycle_counter (used to index
    /// calendars).
    fn advance_metacycle(&mut self) {
        for s in self.scatterers.iter_mut() {
            s.advance_metacycle();
        }

        for g in self.gatherers.iter_mut() {
            g.advance_metacycle();
        }
        self.host_memory.advance_metacycle();
        match BUFFERING {
            BUFFERING_SINGLE => assert_eq!(self.run_config, RunConfig::default()),
            BUFFERING_DOUBLE => self.run_config = self.run_config.toggle(),
            _ => panic!(),
        };
        self.run_entry = 0;
        self.run_cycles = 0;
        self.require_advance_metacycle = false;
    }

    fn set_starting_cycles(&mut self, cycle: Cycle) {
        self.starting_cycles = cycle;
    }

    fn starting_cycles(&self) -> Cycle {
        self.starting_cycles
    }

    fn local_cycles(&self) -> Cycle {
        self.starting_cycles + self.local_cycles
    }

    fn set_crashed(&mut self, crashed: bool) {
        self.crashed = crashed;
    }

    fn get_crashed(&self) -> bool {
        self.crashed
    }
}

impl<const BUFFERING: Buffering> ProvisionedComputeNode<BUFFERING> for ComputeNode<BUFFERING> {
    fn get_node_calendar(&self) -> Option<CalendarVariantRef<BUFFERING>> {
        Some(CalendarVariantRef::Node(&self.node_calendar))
    }

    fn get_scatter_calendar(&self, port: Port) -> Option<CalendarVariantRef<BUFFERING>> {
        let k: usize = port.into();
        assert_eq!(port.direction(), Direction::Incoming);
        self.scatterers[k].get_calendar()
    }

    fn get_gather_calendar(&self, port: Port) -> Option<CalendarVariantRef<BUFFERING>> {
        let k: usize = port.into();
        assert_eq!(port.direction(), Direction::Outgoing);
        self.gatherers[k].get_calendar()
    }

    fn get_host_memory_cfg(&self) -> &HostMemoryCfg<BUFFERING> {
        &self.host_memory.cfg
    }
}

impl<const BUFFERING: usize> VcdComponent for ComputeNode<BUFFERING> {
    fn vcd_write_scope(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_node_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), self.name());
        for i in 0..self.num_inputs() {
            let _vcd_i_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), &i);
            Rc::clone(&writer).borrow_mut().add_var(
                vcd_ext::VarType::Reg,
                self.scatterers[i].frame_size(),
                "input",
                None,
            );
        }
        for i in 0..self.num_outputs() {
            let _vcd_i_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), &i);
            Rc::clone(&writer).borrow_mut().add_var(
                vcd_ext::VarType::Reg,
                self.gatherers[i].frame_size(),
                "output",
                None,
            );
        }
        for (service_id, service) in &self.services {
            if let Some(state) = &service.borrow().persistent_state() {
                let _vcd_service_scope = VcdWriter::managed_decl_scope(
                    Rc::clone(&writer),
                    service_id.to_string().as_str(),
                );
                writer
                    .borrow_mut()
                    .add_var(vcd_ext::VarType::Reg, state.len(), "state", None);
            }
        }
        writer.borrow_mut().add_integer_var::<u32>("metacycles");
        writer.borrow_mut().add_integer_var::<u32>("local_cycles");
        writer
            .borrow_mut()
            .add_integer_var::<u32>("starting_cycles");
        writer.borrow_mut().add_integer_var::<u32>("current_cycles");
        for (i, g) in self.gatherers.iter().enumerate() {
            let _vcd_i_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), &i);
            g.vcd_write_scope(Rc::clone(&writer));
        }
        for (i, s) in self.scatterers.iter().enumerate() {
            let _vcd_i_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), &i);
            s.vcd_write_scope(Rc::clone(&writer));
        }
    }

    fn vcd_init(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_node_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), self.name());
        for (service_id, service) in &self.services {
            if let Some(state) = &service.borrow().persistent_state() {
                let _vcd_service_scope = VcdWriter::managed_decl_scope(
                    Rc::clone(&writer),
                    service_id.to_string().as_str(),
                );
                writer.borrow_mut().change_input_frame_ref(
                    "state",
                    Some(state),
                    state.len(),
                    ChangeValue::Immediately,
                );
            }
        }
        writer
            .borrow_mut()
            .change_vector_immediately("local_cycles", self.local_cycles as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("metacycles", self.metacycle() as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("starting_cycles", self.starting_cycles as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("current_cycles", self.starting_cycles as u32);
        for (i, g) in self.gatherers.iter().enumerate() {
            let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
            g.vcd_init(Rc::clone(&writer));
        }
        for (i, s) in self.scatterers.iter().enumerate() {
            let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
            s.vcd_init(Rc::clone(&writer));
        }
    }
}

impl<const BUFFERING: Buffering> ComputeNode<BUFFERING> {
    pub fn from_config(name: &str, config: &NodeConfiguration) -> Self {
        let mut scatterers = Vec::new();
        for link in config.input_links.iter() {
            scatterers.push(ScatterEngine::<BUFFERING>::new(
                link.frame_size,
                link.memory_size,
                link.calendar_size,
                IOConfig::ComputeIO,
            ));
        }
        let mut gatherers = Vec::new();
        for link in config.output_links.iter() {
            gatherers.push(GatherEngine::<BUFFERING>::new(
                link.frame_size,
                link.memory_size,
                link.calendar_size,
                IOConfig::ComputeIO,
            ));
        }
        Self {
            name: String::from(name),
            services: HashMap::new(),
            scatterers,
            gatherers,
            cycles_per_metacycle: [config.cycles_per_metacycle; BUFFERING],
            local_cycles: 0,
            starting_cycles: config.starting_cycles,
            frequency: Frequency::new(config.frequency),
            mailbox: None,
            node_calendar: [(); BUFFERING].map(|_| vec![]),
            run_config: RunConfig::default(),
            run_entry: 0,
            run_cycles: 0,
            require_advance_metacycle: false,
            host_memory: HostMemory::new(config.memory_size),
            crashed: false,
        }
    }

    fn num_inputs(&self) -> usize {
        self.scatterers.len()
    }
    fn num_outputs(&self) -> usize {
        self.gatherers.len()
    }

    // Read an input from the host memory.
    fn read_input_from_host<'a>(
        &mut self,
        base_address: HostAddress,
        result: &'a mut Data,
    ) -> Option<&'a mut Data> {
        let base_address =
            HostAddress(base_address.0 + self.get_host_memory_cfg().in_mailbox().start);
        let word_size = self.host_memory.cfg.word_size;
        let last_nibble = result.len() % word_size;
        let total_frames_count = (result.len() / word_size + usize::from(last_nibble != 0)) as u32;
        // If the first frame is available, then all frames are available.
        if self.host_memory.read(base_address.clone()).is_none() {
            return None;
        }
        let result_len = result.len();
        for (address, dst) in (0..total_frames_count).zip(result.chunks_mut(word_size)) {
            let read_address = HostAddress(base_address.0 + address as HostAddressType);
            let src = self.host_memory.read(read_address.clone()).expect(
                format!(
                    "read_input of node's host memory {}[{}], mem_size: {} was None.",
                    self.name(),
                    read_address.0,
                    self.host_memory.cfg.memory_size
                )
                .as_str(),
            );
            if address + 1 == total_frames_count && result_len % word_size != 0 {
                let (src, _) = src.split_at(last_nibble);
                dst.clone_from_bitslice(src);
            } else {
                dst.clone_from_bitslice(src);
            }
        }
        Some(result)
    }

    /// Read an input from the given port.
    fn read_input<'a>(
        &mut self,
        port: Port,
        base_address: usize,
        result: &'a mut Data,
    ) -> Option<&'a mut Data> {
        let port_idx: usize = port.into();
        let scatter = &self.scatterers[port_idx];
        let last_nibble = result.len() % scatter.frame_size();
        let total_frames_count =
            result.len() / scatter.frame_size() + usize::from(last_nibble != 0);
        // If the first frame is available, then all frames are available.
        if scatter.memory(base_address).is_none() {
            return None;
        }
        let result_len = result.len();
        for (address, dst) in (0..total_frames_count).zip(result.chunks_mut(scatter.frame_size())) {
            let src = scatter.memory(base_address + address).expect(
                format!(
                    "read_input of node[port] name: {}[{}] address: {} mem_size: {} was None.",
                    self.name(),
                    port_idx,
                    base_address + address,
                    scatter.memory_size(),
                )
                .as_str(),
            );
            if address + 1 == total_frames_count && result_len % scatter.frame_size() != 0 {
                let (src, _) = src.split_at(last_nibble);
                dst.clone_from_bitslice(src);
            } else {
                dst.clone_from_bitslice(src);
            }
        }
        Some(result)
    }

    /// Write the message to the specified port.
    fn write_output_to_host(&mut self, base_address: HostAddress, output: &DataWithValidity) {
        let base_address =
            HostAddress(base_address.0 + self.get_host_memory_cfg().out_mailbox().start);
        let payload = &output.data;
        let word_size = self.host_memory.cfg.word_size;
        let last_nibble = payload.len() % word_size;
        let total_frame_count = (payload.len() / word_size + usize::from(last_nibble != 0)) as u32;
        if !output.valid {
            for address in 0..total_frame_count {
                let dst = self
                    .host_memory
                    .write(&HostAddress(base_address.0 + address as HostAddressType));
                dst.valid = false;
            }
            return;
        }
        for (address, src) in (0..total_frame_count).zip(payload.chunks(word_size)) {
            let dst = self
                .host_memory
                .write(&HostAddress(base_address.0 + address as HostAddressType));
            let dst_data = &mut dst.data;
            dst.valid = true;
            if address + 1 == total_frame_count && last_nibble != 0 {
                let (dst_data, _) = dst_data.split_at_mut(last_nibble);
                dst_data.clone_from_bitslice(src);
            } else {
                dst_data.clone_from_bitslice(src);
            }
        }
    }

    /// Write the message to the specified port.
    fn write_output(
        &mut self,
        port: Port,
        base_address: usize,
        output: &DataWithValidity,
        callbacks: OptionSimCallbacks,
    ) {
        let payload = &output.data;
        let port_idx: usize = port.into();
        let gather = &mut self.gatherers[port_idx];

        let last_nibble = payload.len() % gather.frame_size();
        let total_frame_count = payload.len() / gather.frame_size() + usize::from(last_nibble != 0);
        if !output.valid {
            for address in 0..total_frame_count {
                let dst = gather.memory(base_address + address);
                dst.valid = false;
            }
            return;
        }
        for (address, src) in (0..total_frame_count).zip(payload.chunks(gather.frame_size())) {
            let dst = gather.memory(base_address + address);
            let dst_data = &mut dst.data;
            dst.valid = true;
            if address + 1 == total_frame_count && last_nibble != 0 {
                let (dst_data, _) = dst_data.split_at_mut(last_nibble);
                dst_data.clone_from_bitslice(src);
            } else {
                dst_data.clone_from_bitslice(src);
            }
            callbacks.vcd(|writer| {
                let _vcd_gather_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &port);
                gather.vcd_trace_write(base_address + address, Rc::clone(&writer));
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::calendar::{CalendarEntry, NodeCalendarEntry};
    use crate::hw::scatter::RxMemory;
    use crate::mailbox::{ConnectionAttrs, MappedAttrs};
    use crate::ports;
    use crate::scheduler::CommsHandle;
    use crate::sim::SystemSimulationCallbacks;
    use crate::specs::{ApplicationNode, StatefulNode, SystemContext};
    use crate::Direction;
    use bits::Bits;
    use bits_derive::Bits;
    use serde::{Deserialize, Serialize};

    type FrameSize = u64;

    // the action for this test
    fn incr_counter(
        state: LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        // unpack the local state: where we count the number of invocations.
        let state_bits = &mut state.unwrap_or_else(|| panic!("No state set for incr_counter"));
        let mut invocations = u64::unpack(state_bits.as_bitslice());

        // deserialize the input
        let val = if let Some(bits) = inputs[0] {
            FrameSize::unpack(bits)
        } else {
            0 // on the first cycle(s) there maybe nothing on the input link
        };

        invocations += 1;

        // compute
        let counter = val + invocations;

        log::info!(
            "got: state: {}, input: {}, sending: {}",
            invocations,
            val,
            counter
        );

        // serialize the output
        counter.pack_to(&mut outputs[0].data);
        outputs[0].valid = true;

        invocations.pack_to(state_bits)
    }

    #[test]
    fn test_compute_node() {
        let _logger = env_logger::builder().is_test(true).try_init();

        // 2 nodes; 2 links.
        // Example with two nodes that share one connection (two links)
        //         __              __
        //        /  \  --------> /  \
        //        \__/  <-------- \__/

        // create an application
        let mut app_spec = Application::new();
        let node0 = app_spec.add_node(Service::new(
            "node0",
            incr_counter,
            Some(u64::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        ));
        let node1 = app_spec.add_node(Service::new(
            "node1",
            incr_counter,
            Some(u64::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        ));
        let msg_size = std::mem::size_of::<FrameSize>() * 8;
        let l = Connection::new_for_testing(0, 0, msg_size);
        let conn_0_1 = app_spec.link_simplex_framing(node0, node1, l.clone(), FramingLead::Src);
        let conn_1_0 = app_spec.link_simplex_framing(node1, node0, l.clone(), FramingLead::Src);
        // The app-spec needs to specify message sizes on port properties of the Application.
        for node in [node0, node1] {
            app_spec
                .get_node(node)
                .as_ref()
                .borrow_mut()
                .set_ports_properties(&[
                    (
                        PortLabel::Number(0),
                        PortProperties {
                            frame_size: crate::FrameSize::Computed(RttiType::new::<FrameSize>()),
                            direction: Direction::Incoming,
                            ..Default::default()
                        },
                    ),
                    (
                        PortLabel::Number(1),
                        PortProperties {
                            frame_size: crate::FrameSize::Computed(RttiType::new::<FrameSize>()),
                            direction: Direction::Outgoing,
                            ..Default::default()
                        },
                    ),
                ]);
        }

        // create the hardware topology
        let mut system_spec = HardwareSpec::new();
        const CYCLES_PER_METACYCLE: usize = 3;
        let mut node_config = NodeConfiguration::default();
        node_config.frequency = 1;
        node_config.cycles_per_metacycle = CYCLES_PER_METACYCLE;
        let mut link_config = LinkConfiguration::default();
        link_config.frame_size = std::mem::size_of::<FrameSize>() * 8;
        link_config.memory_size =
            msg_size / link_config.frame_size + usize::from(msg_size % link_config.frame_size != 0);
        node_config.add_link(
            &link_config,
            Port::new(
                0,
                &PortProperties {
                    direction: Direction::Incoming,
                    frame_size: link_config.frame_size.into(),
                    ..Default::default()
                },
            ),
        );
        node_config.add_link(
            &link_config,
            Port::new(
                0,
                &PortProperties {
                    direction: Direction::Outgoing,
                    frame_size: link_config.frame_size.into(),
                    ..Default::default()
                },
            ),
        );
        let mailbox_endpoint_attrs = Some(MappedAttrs {
            base_address: Some(0),
            frame_size: link_config.frame_size,
            memory_size: link_config.memory_size,
            hw_io_index: Some(0),
        });
        let node0_mailbox = MailBox {
            inboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), conn_1_0),
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("node0"),
                mapped_endpoint: mailbox_endpoint_attrs.clone(),
            }],
            outboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), conn_0_1),
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("node0"),
                mapped_endpoint: mailbox_endpoint_attrs.clone(),
            }],
        };
        let node1_mailbox = MailBox {
            inboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), conn_0_1),
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("node1"),
                mapped_endpoint: mailbox_endpoint_attrs.clone(),
            }],
            outboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), conn_1_0),
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("node1"),
                mapped_endpoint: mailbox_endpoint_attrs.clone(),
            }],
        };
        let mut node0_compute = ComputeNode::from_config("node0", &node_config);
        node0_compute.set_mailbox(node0_mailbox);
        assert_eq!(node0_compute.gatherers[0].memory_size(), 1);
        assert_eq!(node0_compute.scatterers[0].memory_size(), 1);
        assert_eq!(node0_compute.gatherers[0].frame_size(), 64);
        assert_eq!(node0_compute.scatterers[0].frame_size(), 64);
        let node0 = system_spec.add_node(Node::ComputeNode(node0_compute));
        let mut node1_compute = ComputeNode::from_config("node1", &node_config);
        node1_compute.set_mailbox(node1_mailbox);
        assert_eq!(node1_compute.gatherers[0].memory_size(), 1);
        assert_eq!(node1_compute.scatterers[0].memory_size(), 1);
        assert_eq!(node1_compute.gatherers[0].frame_size(), 64);
        assert_eq!(node1_compute.scatterers[0].frame_size(), 64);
        let node1 = system_spec.add_node(Node::ComputeNode(node1_compute));

        let l = Link::from_config(
            0,
            0,
            LinkConfiguration {
                latency: 1,
                frame_size: link_config.frame_size,
                ..Default::default()
            },
        );
        system_spec.link_simplex(node0, node1, l.clone());
        system_spec.link_simplex(node1, node0, l.clone());

        // assign action functions and calendars (the AppSpec placeholder)
        // for each node, setup the action, and calendars that have a single
        // entry sending a single frame.
        for node_id in system_spec.iter_nodes() {
            let node = system_spec.get_node(node_id);
            let (n_inputs, n_outputs) = system_spec.get_node_inout_count(node_id);

            node.borrow_mut().register_app(
                ServiceHandle::new(app_spec.id(), node_id),
                Rc::clone(&app_spec.get_node(node_id)),
            );
            node.borrow_mut().set_calendar(CalendarVariant::Node([
                vec![
                    NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE - 1),
                    NodeCalendarEntry::new(Some(ServiceHandle::new(app_spec.id(), node_id)), 1),
                ],
                vec![NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE)],
            ]));

            for p in 0..n_inputs {
                node.borrow_mut().into_mut_provisioned_node().unwrap().set_io_calendar(
                    IOCalendarVariant::Input([
                        vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                        vec![CalendarEntry::new(Some(0), 1), CalendarEntry::new(None, 2)],
                    ]),
                    // We specify port-properties here explicitly because in a
                    // real application they would be set on the Port.
                    Port::new(
                        p,
                        &PortProperties {
                            direction: Direction::Incoming,
                            frame_size: ports::FrameSize::Computed(RttiType::new::<FrameSize>()),
                            ..PortProperties::default()
                        },
                    ),
                );
            }
            for p in 0..n_outputs {
                node.borrow_mut().into_mut_provisioned_node().unwrap().set_io_calendar(
                    IOCalendarVariant::Output([
                        vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                        vec![CalendarEntry::new(Some(0), 1), CalendarEntry::new(None, 2)],
                    ]),
                    Port::new(
                        p,
                        &PortProperties {
                            direction: Direction::Outgoing,
                            frame_size: ports::FrameSize::Computed(RttiType::new::<FrameSize>()),
                            ..PortProperties::default()
                        },
                    ),
                );
            }
        }

        log::debug!("system spec:\n{}", system_spec.to_graphviz());
        let mut simulation =
            HardwareSystemSimulation::new(&system_spec, FailureProperties::default());
        let sim_cpm = simulation.sim_cycles_per_metacycle(&system_spec);
        // In this test, each node's compute CPM is what determines the simulation cpm.
        assert_eq!(sim_cpm, [CYCLES_PER_METACYCLE, CYCLES_PER_METACYCLE]);
        let cycles = 43 * 2 * CYCLES_PER_METACYCLE;
        let mut callbacks = SystemSimulationCallbacks::create_vcd_callbacks();
        callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::write_header(writer, &system_spec));
        for cycle in 0..cycles {
            log::info!("cycle {}", cycle);
            simulation.simulate_system_one_cycle(&system_spec, &mut callbacks);
        }
        callbacks
            .get_vcd_writer()
            .map(|writer| writer.borrow_mut().flush_after_simulation());

        for node_id in app_spec.iter_nodes() {
            let node = app_spec.get_node(node_id);
            assert_eq!(
                u64::unpack(node.borrow().persistent_state().unwrap()),
                ((cycles / CYCLES_PER_METACYCLE) / 2) as u64
            );
        }
        for node_id in system_spec.iter_nodes() {
            assert_eq!(
                system_spec.get_node(node_id).borrow().metacycle(),
                cycles / CYCLES_PER_METACYCLE
            );
        }
    }

    #[derive(Bits, Serialize, Deserialize, Clone, Copy, Debug)]
    struct Inner {
        v: u32,
        w: u8,
    }

    #[derive(Bits, Serialize, Deserialize, Clone, Copy, Debug)]
    struct MessageAligned {
        x: u32,
    }

    impl Default for MessageAligned {
        fn default() -> Self {
            Self { x: 0xabcdef12 }
        }
    }

    #[derive(Bits, Serialize, Deserialize, Clone, Copy, Debug)]
    struct Message {
        x: bool,
        y: u32,
        inner: Inner,
    }

    impl Default for Message {
        fn default() -> Self {
            Self {
                x: false,
                y: 0xcafef00d,
                inner: Inner {
                    v: 0x12345678,
                    w: 0xba,
                },
            }
        }
    }

    #[derive(Bits, Serialize, Deserialize, Clone, Copy, Debug)]
    struct MessageLarge {
        w: [u32; 20],
        // x: [u32; 20],
        // y: [u32; 20],
        // z: [u8; 17],
    }

    impl Default for MessageLarge {
        fn default() -> Self {
            Self {
                w: [3; 20],
                // x: [0; 20],
                // y: [1; 20],
                // z: [2; 17],
            }
        }
    }

    fn read_input_tester<T>(hw_frame_size: usize, base_address: usize)
    where
        T: Serialize + Bits + Default,
    {
        let msg = T::default();
        let mut msg_bits: Data = BitVec::repeat(false, <T as Bits>::SIZE).into_boxed_bitslice();
        msg.pack_to(&mut msg_bits);
        let last_nibble = msg_bits.len() % hw_frame_size;
        let memory_size =
            base_address + msg_bits.len() / hw_frame_size + usize::from(last_nibble != 0);
        let mut memory_contents: RxMemory = msg_bits
            .chunks(hw_frame_size)
            .map(|c| {
                let mut frame: Data = BitVec::repeat(false, hw_frame_size).into_boxed_bitslice();
                if c.len() < hw_frame_size {
                    let (dst, _) = frame.split_at_mut(c.len());
                    dst.clone_from_bitslice(c);
                } else {
                    frame.clone_from_bitslice(c);
                }
                Some(frame)
            })
            .collect::<Vec<_>>();
        let mut memory: RxMemory = vec![None; base_address];
        memory.append(&mut memory_contents);
        assert_eq!(memory.len(), memory_size);

        let mut test_node = ComputeNode::<{ BUFFERING_DOUBLE }>::from_config(
            "test_node",
            &NodeConfiguration {
                input_links: vec![LinkConfiguration {
                    frame_size: hw_frame_size,
                    calendar_size: 2,
                    memory_size: memory_size,
                    ..Default::default()
                }],
                ..Default::default()
            },
        );
        test_node.scatterers[0].debug_set_memory_1(&memory);
        let mut recovered_msg_bits: Data =
            BitVec::repeat(false, <T as Bits>::SIZE).into_boxed_bitslice();
        test_node.read_input(Port::from(0), base_address, &mut recovered_msg_bits);
        assert_eq!(recovered_msg_bits.as_bitslice(), msg_bits.as_bitslice());
    }

    #[test]
    fn test_read_input() {
        read_input_tester::<Message>(1, 0);
        read_input_tester::<Message>(2, 0);
        read_input_tester::<Message>(3, 0);
        read_input_tester::<Message>(5, 0);
        read_input_tester::<Message>(7, 0);
        read_input_tester::<Message>(11, 0);
        read_input_tester::<Message>(8, 0);
        read_input_tester::<Message>(16, 0);
        read_input_tester::<Message>(32, 0);
        read_input_tester::<Message>(64, 0);
        read_input_tester::<Message>(2048, 0);
        read_input_tester::<MessageAligned>(1, 0);
        read_input_tester::<MessageAligned>(2, 0);
        read_input_tester::<MessageAligned>(3, 0);
        read_input_tester::<MessageAligned>(5, 0);
        read_input_tester::<MessageAligned>(7, 0);
        read_input_tester::<MessageAligned>(11, 0);
        read_input_tester::<MessageAligned>(8, 0);
        read_input_tester::<MessageAligned>(16, 0);
        read_input_tester::<MessageAligned>(32, 0);
        read_input_tester::<MessageAligned>(64, 0);
        read_input_tester::<MessageAligned>(2048, 0);
        read_input_tester::<MessageLarge>(1, 0);
        read_input_tester::<MessageLarge>(2, 0);
        read_input_tester::<MessageLarge>(3, 0);
        read_input_tester::<MessageLarge>(5, 0);
        read_input_tester::<MessageLarge>(7, 0);
        read_input_tester::<MessageLarge>(11, 0);
        read_input_tester::<MessageLarge>(8, 0);
        read_input_tester::<MessageLarge>(16, 0);
        read_input_tester::<MessageLarge>(32, 0);
        read_input_tester::<MessageLarge>(64, 0);
        read_input_tester::<MessageLarge>(2048, 0);

        read_input_tester::<Message>(1, 1);
        read_input_tester::<Message>(2, 2);
        read_input_tester::<Message>(3, 3);
        read_input_tester::<Message>(5, 4);
        read_input_tester::<Message>(7, 5);
        read_input_tester::<Message>(11, 6);
        read_input_tester::<Message>(8, 7);
        read_input_tester::<Message>(16, 8);
        read_input_tester::<Message>(32, 9);
        read_input_tester::<Message>(64, 10);
        read_input_tester::<Message>(2048, 11);
        read_input_tester::<MessageAligned>(1, 1);
        read_input_tester::<MessageAligned>(2, 2);
        read_input_tester::<MessageAligned>(3, 3);
        read_input_tester::<MessageAligned>(5, 4);
        read_input_tester::<MessageAligned>(7, 5);
        read_input_tester::<MessageAligned>(11, 6);
        read_input_tester::<MessageAligned>(8, 7);
        read_input_tester::<MessageAligned>(16, 8);
        read_input_tester::<MessageAligned>(32, 9);
        read_input_tester::<MessageAligned>(64, 10);
        read_input_tester::<MessageAligned>(2048, 11);
        read_input_tester::<MessageLarge>(1, 1);
        read_input_tester::<MessageLarge>(2, 2);
        read_input_tester::<MessageLarge>(3, 3);
        read_input_tester::<MessageLarge>(5, 4);
        read_input_tester::<MessageLarge>(7, 5);
        read_input_tester::<MessageLarge>(11, 6);
        read_input_tester::<MessageLarge>(8, 7);
        read_input_tester::<MessageLarge>(16, 8);
        read_input_tester::<MessageLarge>(32, 9);
        read_input_tester::<MessageLarge>(64, 10);
        read_input_tester::<MessageLarge>(2048, 11);
    }

    fn write_output_tester<T>(hw_frame_size: usize, base_address: usize)
    where
        T: Serialize + Default + Bits,
    {
        let msg = T::default();
        let msg_size = <T as Bits>::SIZE;
        let last_nibble = msg_size % hw_frame_size;
        let memory_size = base_address + msg_size / hw_frame_size + usize::from(last_nibble != 0);
        let mut test_node = ComputeNode::<{ BUFFERING_DOUBLE }>::from_config(
            "test_node",
            &NodeConfiguration {
                output_links: vec![LinkConfiguration {
                    frame_size: hw_frame_size,
                    calendar_size: 2,
                    memory_size: memory_size,
                    ..Default::default()
                }],
                ..Default::default()
            },
        );
        let output = DataWithValidity {
            data: msg.pack().into_boxed_bitslice(),
            valid: true,
        };
        test_node.write_output(
            Port::from(0),
            base_address,
            &output,
            &mut SystemSimulationCallbacks::default(),
        );
        let tx_memory = test_node.gatherers[0].debug_get_memory_1();
        assert_eq!(tx_memory.len(), memory_size);
        for (address, chunk) in output.data.chunks(hw_frame_size).enumerate() {
            let frame = &tx_memory[base_address + address];
            assert!(frame.valid);
            let frame_data = &frame.data;
            if chunk.len() < hw_frame_size {
                let (frame_data, _) = frame_data.split_at(last_nibble);
                assert_eq!(frame_data, chunk);
            } else {
                assert_eq!(frame_data, chunk);
            }
        }
    }

    #[test]
    fn test_write_output() {
        write_output_tester::<Message>(1, 0);
        write_output_tester::<Message>(2, 0);
        write_output_tester::<Message>(3, 0);
        write_output_tester::<Message>(5, 0);
        write_output_tester::<Message>(7, 0);
        write_output_tester::<Message>(11, 0);
        write_output_tester::<Message>(8, 0);
        write_output_tester::<Message>(16, 0);
        write_output_tester::<Message>(32, 0);
        write_output_tester::<Message>(64, 0);
        write_output_tester::<Message>(2048, 0);
        write_output_tester::<MessageAligned>(1, 0);
        write_output_tester::<MessageAligned>(2, 0);
        write_output_tester::<MessageAligned>(3, 0);
        write_output_tester::<MessageAligned>(5, 0);
        write_output_tester::<MessageAligned>(7, 0);
        write_output_tester::<MessageAligned>(11, 0);
        write_output_tester::<MessageAligned>(8, 0);
        write_output_tester::<MessageAligned>(16, 0);
        write_output_tester::<MessageAligned>(32, 0);
        write_output_tester::<MessageAligned>(64, 0);
        write_output_tester::<MessageAligned>(2048, 0);

        write_output_tester::<Message>(1, 1);
        write_output_tester::<Message>(2, 2);
        write_output_tester::<Message>(3, 3);
        write_output_tester::<Message>(5, 4);
        write_output_tester::<Message>(7, 5);
        write_output_tester::<Message>(11, 6);
        write_output_tester::<Message>(8, 7);
        write_output_tester::<Message>(16, 8);
        write_output_tester::<Message>(32, 9);
        write_output_tester::<Message>(64, 10);
        write_output_tester::<Message>(2048, 11);
        write_output_tester::<MessageAligned>(1, 1);
        write_output_tester::<MessageAligned>(2, 2);
        write_output_tester::<MessageAligned>(3, 3);
        write_output_tester::<MessageAligned>(5, 4);
        write_output_tester::<MessageAligned>(7, 5);
        write_output_tester::<MessageAligned>(11, 6);
        write_output_tester::<MessageAligned>(8, 7);
        write_output_tester::<MessageAligned>(16, 8);
        write_output_tester::<MessageAligned>(32, 9);
        write_output_tester::<MessageAligned>(64, 10);
        write_output_tester::<MessageAligned>(2048, 11);
    }

    fn write_read_tester<T>(hw_frame_size: usize, base_address: usize)
    where
        T: Default + Serialize + Bits,
    {
        let msg_size = <T as Bits>::SIZE;
        let memory_size =
            base_address + msg_size / hw_frame_size + usize::from(msg_size % hw_frame_size != 0);
        let mut test_node = ComputeNode::<{ BUFFERING_DOUBLE }>::from_config(
            "test_node",
            &NodeConfiguration {
                output_links: vec![LinkConfiguration {
                    frame_size: hw_frame_size,
                    calendar_size: 2,
                    memory_size: memory_size,
                    ..Default::default()
                }],
                input_links: vec![LinkConfiguration {
                    frame_size: hw_frame_size,
                    calendar_size: 2,
                    memory_size: memory_size,
                    ..Default::default()
                }],
                ..Default::default()
            },
        );
        let msg = T::default();
        let output = DataWithValidity {
            data: msg.pack().into_boxed_bitslice(),
            valid: true,
        };
        test_node.write_output(
            Port::from(0),
            base_address,
            &output,
            &mut SystemSimulationCallbacks::default(),
        );
        let mut tx_mem = test_node.gatherers[0].debug_get_memory_1();
        let mut rx_mem: RxMemory = vec![];
        for (i, dv) in tx_mem.drain(..).enumerate() {
            if i >= base_address {
                assert!(dv.valid);
            }
            rx_mem.push(Some(dv.data));
        }
        test_node.scatterers[0].debug_set_memory_1(&rx_mem);
        let mut recovered: Data = BitVec::repeat(false, msg_size).into_boxed_bitslice();
        test_node.read_input(Port::from(0), base_address, &mut recovered);
        assert_eq!(recovered, output.data);
    }

    #[test]
    fn test_read_write() {
        write_read_tester::<Message>(1, 0);
        write_read_tester::<Message>(2, 0);
        write_read_tester::<Message>(3, 0);
        write_read_tester::<Message>(5, 0);
        write_read_tester::<Message>(7, 0);
        write_read_tester::<Message>(11, 0);
        write_read_tester::<Message>(8, 0);
        write_read_tester::<Message>(16, 0);
        write_read_tester::<Message>(32, 0);
        write_read_tester::<Message>(64, 0);
        write_read_tester::<MessageAligned>(2048, 0);
        write_read_tester::<MessageAligned>(1, 0);
        write_read_tester::<MessageAligned>(2, 0);
        write_read_tester::<MessageAligned>(3, 0);
        write_read_tester::<MessageAligned>(5, 0);
        write_read_tester::<MessageAligned>(7, 0);
        write_read_tester::<MessageAligned>(11, 0);
        write_read_tester::<MessageAligned>(8, 0);
        write_read_tester::<MessageAligned>(16, 0);
        write_read_tester::<MessageAligned>(32, 0);
        write_read_tester::<MessageAligned>(64, 0);
        write_read_tester::<MessageAligned>(2048, 0);
        write_read_tester::<MessageLarge>(1, 0);
        write_read_tester::<MessageLarge>(2, 0);
        write_read_tester::<MessageLarge>(3, 0);
        write_read_tester::<MessageLarge>(5, 0);
        write_read_tester::<MessageLarge>(7, 0);
        write_read_tester::<MessageLarge>(11, 0);
        write_read_tester::<MessageLarge>(8, 0);
        write_read_tester::<MessageLarge>(16, 0);
        write_read_tester::<MessageLarge>(32, 0);
        write_read_tester::<MessageLarge>(64, 0);
        write_read_tester::<MessageLarge>(2048, 0);

        write_read_tester::<Message>(1, 1);
        write_read_tester::<Message>(2, 2);
        write_read_tester::<Message>(3, 3);
        write_read_tester::<Message>(5, 4);
        write_read_tester::<Message>(7, 5);
        write_read_tester::<Message>(11, 6);
        write_read_tester::<Message>(8, 7);
        write_read_tester::<Message>(16, 8);
        write_read_tester::<Message>(32, 9);
        write_read_tester::<Message>(64, 10);
        write_read_tester::<MessageAligned>(2048, 1);
        write_read_tester::<MessageAligned>(1, 2);
        write_read_tester::<MessageAligned>(2, 3);
        write_read_tester::<MessageAligned>(3, 4);
        write_read_tester::<MessageAligned>(5, 5);
        write_read_tester::<MessageAligned>(7, 6);
        write_read_tester::<MessageAligned>(11, 7);
        write_read_tester::<MessageAligned>(8, 8);
        write_read_tester::<MessageAligned>(16, 9);
        write_read_tester::<MessageAligned>(32, 10);
        write_read_tester::<MessageAligned>(64, 11);
        write_read_tester::<MessageAligned>(2048, 12);
        write_read_tester::<MessageLarge>(1, 1);
        write_read_tester::<MessageLarge>(2, 2);
        write_read_tester::<MessageLarge>(3, 3);
        write_read_tester::<MessageLarge>(5, 4);
        write_read_tester::<MessageLarge>(7, 5);
        write_read_tester::<MessageLarge>(11, 6);
        write_read_tester::<MessageLarge>(8, 7);
        write_read_tester::<MessageLarge>(16, 8);
        write_read_tester::<MessageLarge>(32, 9);
        write_read_tester::<MessageLarge>(64, 10);
        write_read_tester::<MessageLarge>(2048, 11);
    }

    #[test]
    fn test_double_buffered_host_memory_cfg() {
        let memory_size = 0xffffffff;
        let mut mem_cfg = HostMemoryCfg::<BUFFERING_DOUBLE>::new(8, memory_size);
        let start_address = memory_size - 4 * HOST_MEMORY_MAILBOX_SIZE;
        let mailbox_0_0 = (start_address + 0 * HOST_MEMORY_MAILBOX_SIZE) as HostAddressType;
        let mailbox_0_1 = (start_address + 1 * HOST_MEMORY_MAILBOX_SIZE) as HostAddressType;
        let mailbox_1_0 = (start_address + 2 * HOST_MEMORY_MAILBOX_SIZE) as HostAddressType;
        let mailbox_1_1 = (start_address + 3 * HOST_MEMORY_MAILBOX_SIZE) as HostAddressType;

        assert_eq!(mem_cfg.run_config, RunConfig::RunCalendar0);
        assert_eq!(mem_cfg.out_mailbox().start, mailbox_0_0);
        assert_eq!(mem_cfg.in_mailbox().start, mailbox_0_1);
        mem_cfg.advance_metacycle();
        assert_eq!(mem_cfg.run_config, RunConfig::RunCalendar1);
        assert_eq!(mem_cfg.out_mailbox().start, mailbox_1_0);
        assert_eq!(mem_cfg.in_mailbox().start, mailbox_1_1);
        mem_cfg.advance_metacycle();
        assert_eq!(mem_cfg.run_config, RunConfig::RunCalendar0);
        assert_eq!(mem_cfg.out_mailbox().start, mailbox_0_1);
        assert_eq!(mem_cfg.in_mailbox().start, mailbox_0_0);
        mem_cfg.advance_metacycle();
        assert_eq!(mem_cfg.run_config, RunConfig::RunCalendar1);
        assert_eq!(mem_cfg.out_mailbox().start, mailbox_1_1);
        assert_eq!(mem_cfg.in_mailbox().start, mailbox_1_0);
        mem_cfg.advance_metacycle();
        assert_eq!(mem_cfg.run_config, RunConfig::RunCalendar0);
        assert_eq!(mem_cfg.out_mailbox().start, mailbox_0_0);
        assert_eq!(mem_cfg.in_mailbox().start, mailbox_0_1);
    }
}
