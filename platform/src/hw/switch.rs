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

use super::*;
use crate::app::ServiceHandle;
use crate::calendar::Calendar;
use crate::calendar::CalendarVariantRef;
use crate::calendar::IOCalendarVariant;
use ::vcd as vcd_ext;
use calendar::Buffering;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::convert::Into;
use std::rc::Rc;

use crate::hw::ports::Port;
use crate::hw::RunConfig;
use crate::sim::OptionSimCallbacks;
use crate::specs::ProvisionedNode;
use crate::vcd::{ChangeValue, VcdComponent, VcdWriter};
use crate::NodeSpec;
use calendar::CrossbarCalendar;
use config::SwitchConfiguration;

#[derive(Clone, Debug)]
pub struct Crossbar<const BUFFERING: Buffering> {
    calendar: [CrossbarCalendar; BUFFERING],
    /// The current calendar entry.
    entry_ptr: usize,
    /// The number of frames processed at the current entry-pointer.
    frame_count: usize,
    /// The number of outputs from the crossbar.
    output_count: usize,
    run_config: RunConfig,
    require_advance_metacycle: bool,
}

impl<const BUFFERING: Buffering> Default for Crossbar<BUFFERING> {
    fn default() -> Self {
        Crossbar {
            calendar: [(); BUFFERING].map(|_| vec![]),
            entry_ptr: 0,
            frame_count: 0,
            output_count: 0,
            run_config: RunConfig::default(),
            require_advance_metacycle: false,
        }
    }
}

/// Populates a vector of output data frames by selecting from the input data
/// frames, as described by the crossbar-calendar's current entry.
impl<const BUFFERING: Buffering> Crossbar<BUFFERING> {
    pub fn step(
        &mut self,
        input: &Vec<InputFrameRef>,
        output: &mut Vec<OutputFrameRef>,
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        if self.require_advance_metacycle {
            return Err(Error::OutOfCalendar);
        }
        let run_config_usize: usize = self.run_config.clone().into();
        let calendar_len = self.calendar[run_config_usize].len();
        if self.entry_ptr >= self.calendar[run_config_usize].len() {
            return Err(Error::InvalidAddress);
        }
        assert!(match BUFFERING {
            BUFFERING_SINGLE => self.run_config == RunConfig::default(),
            _ => true,
        });
        log::debug!(
            ">>> crossbar inputs: {:?}, calendar: {:?}",
            input,
            self.calendar[run_config_usize][self.entry_ptr]
        );
        let calendar_entry = match self.run_config {
            RunConfig::RunCalendar0 => &self.calendar[0][self.entry_ptr],
            RunConfig::RunCalendar1 => &self.calendar[1][self.entry_ptr],
        };
        callbacks.vcd(|writer| {
            let _vcd_crossbar_scope =
                VcdWriter::managed_trace_scope(Rc::clone(&writer), "crossbar");
            calendar_entry.input_source.as_ref().map(|input_source| {
                for (i, src) in input_source.iter().enumerate() {
                    writer
                        .borrow_mut()
                        .change_vector_immediately(format!("\\input_source[{}]", i).as_str(), *src);
                }
            });
        });
        assert!(self.frame_count < calendar_entry.frame_count as usize);
        if let Some(input_source) = &calendar_entry.input_source {
            if output.len() != input_source.len() {
                log::debug!(
                    "Output len {}, input_source len {}",
                    output.len(),
                    input_source.len()
                );
                return Err(Error::InvalidCalendar);
            }
            for (i, src) in input_source.iter().enumerate() {
                if *src as usize >= input.len() {
                    return Err(Error::InvalidAddress);
                }
                if let Some(data) = input[*src as usize] {
                    *output[i] = DataWithValidity {
                        data: data.clone(),
                        valid: true,
                    }
                } else {
                    *output[i] = DataWithValidity {
                        data: Default::default(),
                        valid: false,
                    };
                }
            }
        }

        // Advance calendar to the next entry after exhausting the current entry.
        if self.frame_count + 1 == calendar_entry.frame_count as usize {
            self.frame_count = 0;
            if self.entry_ptr + 1 == calendar_len {
                self.require_advance_metacycle = true;
            }
            self.entry_ptr = (self.entry_ptr + 1) % calendar_len;
        } else {
            self.frame_count += 1;
        }

        callbacks.vcd(|writer| {
            let _vcd_crossbar_scope =
                VcdWriter::managed_trace_scope(Rc::clone(&writer), "crossbar");
            writer
                .borrow_mut()
                .change_vector("entry_ptr", self.entry_ptr as u32);
            writer
                .borrow_mut()
                .change_vector("frame_count", self.frame_count as u32);
        });
        log::debug!("<<< crossbar {:?}", output);
        Ok(())
    }

    fn advance_metacycle(&mut self) {
        assert!(
            self.require_advance_metacycle,
            "entry_ptr {} frame_count {} run_config {:?} calendar {:?}",
            self.entry_ptr,
            self.frame_count,
            self.run_config,
            self.calendar[self.run_config.clone() as usize]
        );
        self.entry_ptr = 0;
        self.frame_count = 0;
        match BUFFERING {
            BUFFERING_SINGLE => assert_eq!(self.run_config, RunConfig::default()),
            BUFFERING_DOUBLE => self.run_config = self.run_config.toggle(),
            _ => panic!(),
        };
        self.require_advance_metacycle = false;
    }
}

impl<const BUFFERING: Buffering> VcdComponent for Crossbar<BUFFERING> {
    fn vcd_write_scope(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_crossbar_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), "crossbar");
        writer.borrow_mut().add_integer_var::<u32>("entry_ptr");
        writer.borrow_mut().add_integer_var::<u32>("frame_count");
        for crossbar_idx in 0..BUFFERING {
            for i in 0..self.output_count {
                writer.borrow_mut().add_integer_var::<u32>(
                    format!("\\input_source_{}[{}]", crossbar_idx, i).as_str(),
                )
            }
        }
    }

    fn vcd_init(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_crossbar_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), "crossbar");
        writer
            .borrow_mut()
            .change_vector_immediately("entry_ptr", self.entry_ptr as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("frame_count", self.frame_count as u32);
        for crossbar_idx in 0..BUFFERING {
            let first_calendar = &self.calendar[crossbar_idx][self.entry_ptr];
            if let Some(input_source) = &first_calendar.input_source {
                for (i, src) in input_source.iter().enumerate() {
                    writer.borrow_mut().change_vector_immediately(
                        format!("\\input_source_{}[{}]", crossbar_idx, i).as_str(),
                        *src,
                    )
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SwitchType {
    /// Switches with a single register on their IO interface.
    Registered,

    /// Switches with a circular buffer on their IO interface.
    RoundRobin,
}

#[derive(Clone, Debug)]
pub struct SwitchNode<const BUFFERING: Buffering> {
    name: String,
    /// input links: scatter engines, one for each input link, indexed by `port`.
    scatterers: Vec<ScatterEngine<BUFFERING>>,
    /// output links: gather engines, one for each output link, indexed by `port`
    gatherers: Vec<GatherEngine<BUFFERING>>,
    /// boottime value: how many local cycles are in a metacycle.
    cycles_per_metacycle: [Cycle; BUFFERING],
    /// local cycle counter
    local_cycles: Cycle,
    /// See `ComputeNode::starting_cycles`.
    starting_cycles: Cycle,
    // required by the NodeSpec trait
    frequency: Frequency,
    crossbar: Crossbar<BUFFERING>,
    /// The number of cycles it takes to traverse the crossbar.
    crossbar_latency: Cycle,
    crossbar_latency_queues: Vec<VecDeque<Option<Data>>>,
    switch_type: SwitchType,
    crashed: bool,
}

impl<const BUFFERING: Buffering> NodeSpec<BUFFERING> for SwitchNode<BUFFERING> {
    fn step(
        &mut self,
        _inputs: &[InputFrameRef],
        _outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        if self.crashed {
            log::trace!(
                "Skipping step() for crashed switch node name: \"{}\"",
                self.name(),
            );
            return Ok(());
        }
        let _vcd_node_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(writer, self.name()));
        let mut input_frames = self
            .scatterers
            .iter()
            .map(|engine| engine.memory(0))
            .collect::<Vec<_>>();
        for i in 0..self.scatterers.len() {
            log::trace!("scatter[{}]\n{:#?}", i, self.scatterers[i]);
        }
        let mut latency_queues_head: Vec<Option<Data>> = vec![];
        if self.crossbar_latency > 0 {
            // If the crossbar has latency, we push the contents of the input
            // frames onto the latency queues and pop the head of each latency
            // queue.
            assert_eq!(self.crossbar_latency_queues.len(), self.scatterers.len());
            assert!(self
                .crossbar_latency_queues
                .iter()
                .all(|q| q.len() == self.crossbar_latency));
            for (i, frame) in input_frames.iter().enumerate() {
                self.crossbar_latency_queues[i].push_back(frame.map(|data| data.clone()));
                latency_queues_head.push(
                    self.crossbar_latency_queues[i]
                        .pop_front()
                        .expect("crossbar latency queues should never be empty"),
                );
                callbacks.vcd(|writer| {
                    for queue_idx in 0..self.crossbar_latency {
                        writer.borrow_mut().change_input_frame_ref(
                            format!("\\delay[{}][{}]", i, queue_idx).as_str(),
                            self.crossbar_latency_queues[i][queue_idx].as_ref(),
                            self.scatterers[i].frame_size(),
                            ChangeValue::Defer,
                        );
                    }
                });
            }
            if log::log_enabled!(log::Level::Debug) {
                for (i, q) in self.crossbar_latency_queues.iter().enumerate() {
                    log::debug!("Queue {}: {:?}", i, q);
                }
            }
            input_frames = latency_queues_head
                .iter()
                .map(|q| q.as_ref())
                .collect::<Vec<_>>();
        }

        let gatherers_count = self.gatherers.len();
        let mut output_frame_refs = self
            .gatherers
            .iter_mut()
            .map(|engine| engine.memory(0))
            .collect();
        self.crossbar
            .step(&input_frames, &mut output_frame_refs, callbacks)?;
        assert_eq!(gatherers_count, output_frame_refs.len());

        if let Some(writer) = callbacks.get_vcd_writer() {
            for (i, gather) in self.gatherers.iter().enumerate() {
                let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
                gather.vcd_trace_write(0, Rc::clone(&writer))
            }
        }

        self.local_cycles += 1;
        callbacks.vcd(|writer| {
            writer
                .borrow_mut()
                .change_vector("local_cycles", self.local_cycles as u32);
            writer
                .borrow_mut()
                .change_vector("starting_cycles", self.starting_cycles as u32);
            writer
                .borrow_mut()
                .change_vector("current_cycles", self.local_cycles() as u32);
        });
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

    fn into_provisioned_switch_node(&self) -> Option<&dyn ProvisionedSwitchNode<BUFFERING>> {
        Some(self)
    }

    fn into_mut_provisioned_switch_node(
        &mut self,
    ) -> Option<&mut dyn ProvisionedSwitchNode<BUFFERING>> {
        Some(self)
    }
}

// Switches use the same SW infra to implement their functional behavior but
// their input/output calendars are implemented in HW as counters that round-robin
// access to their respective memories.
fn is_round_robin_calendar(calendar: &Calendar, memory_size: usize) -> bool {
    calendar.len() == memory_size
        && calendar
            .iter()
            .enumerate()
            .all(|(i, entry)| entry.base_address == Some(i as u32) && entry.frame_count == 1)
}

fn is_register_calendar(calendar: &Calendar) -> bool {
    calendar.iter().all(|entry| {
        (entry.base_address.is_none() && entry.frame_count > 0)
            || (entry.base_address.is_some()
                && entry.base_address.unwrap() == 0
                && entry.frame_count == 1)
    })
}

impl<const BUFFERING: Buffering> ProvisionedSwitchNode<BUFFERING> for SwitchNode<BUFFERING> {
    fn crossbar_latency(&self) -> Latency {
        Latency(self.crossbar_latency)
    }

    fn get_crossbar_calendar(&self) -> Option<CalendarVariantRef<BUFFERING>> {
        return Some(CalendarVariantRef::Crossbar(&self.crossbar.calendar));
    }

    fn switch_type(&self) -> SwitchType {
        self.switch_type.clone()
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
}

/// Infers the type of switch based on the contents of the calendar.
fn infer_switch_type(calendar: &Vec<CalendarEntry>, memory_size: usize) -> SwitchType {
    if is_round_robin_calendar(calendar, memory_size) {
        SwitchType::RoundRobin
    } else if is_register_calendar(calendar) {
        SwitchType::Registered
    } else {
        panic!(
            "Switch calendars must either be round-robin or registered. Got {:?}",
            calendar
        );
    }
}

impl<const BUFFERING: Buffering> ProvisionedNode<BUFFERING> for SwitchNode<BUFFERING> {
    fn cycles_per_metacycle(&self) -> [Cycle; BUFFERING] {
        self.cycles_per_metacycle
    }
    fn set_cycles_per_metacycle(&mut self, cpm: [Cycle; BUFFERING]) {
        self.cycles_per_metacycle = cpm;
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

    fn metacycle(&self) -> Cycle {
        crate::hw::metacycle(self.local_cycles, self.cycles_per_metacycle)
    }

    fn set_io_calendar(&mut self, calendar_variant: IOCalendarVariant<BUFFERING>, port: Port) {
        let port_idx: usize = port.into();
        match &calendar_variant {
            IOCalendarVariant::Input(calendar) => {
                let switch_type =
                    infer_switch_type(&calendar[0], self.scatterers[port_idx].memory_size());
                assert!(calendar.iter().all(|c| infer_switch_type(
                    c,
                    self.scatterers[port_idx].memory_size()
                ) == switch_type));
                self.switch_type = switch_type;
                self.scatterers[port_idx].set_calendar(calendar_variant);
            }
            IOCalendarVariant::Output(calendar) => {
                let switch_type =
                    infer_switch_type(&calendar[0], self.gatherers[port_idx].memory_size());
                assert!(calendar.iter().all(|c| infer_switch_type(
                    c,
                    self.gatherers[port_idx].memory_size()
                ) == switch_type));
                self.switch_type = switch_type;
                self.gatherers[port_idx].set_calendar(calendar_variant);
            }
        };
    }

    fn register_app(&mut self, _service_handle: ServiceHandle, _service: Rc<RefCell<Service>>) {
        // TODO(cascaval) should not get here!
        unimplemented!();
    }
    fn frequency(&self) -> Frequency {
        self.frequency
    }
    fn set_frequency(&mut self, freq: Frequency) {
        self.frequency = freq;
    }
    fn set_calendar(&mut self, calendar_variant: CalendarVariant<BUFFERING>) {
        match &calendar_variant {
            CalendarVariant::Crossbar(calendar) => self.crossbar.calendar = calendar.to_owned(),
            _ => panic!("Incompatible calendar variant for switch."),
        }
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

        // Step the gather-memories, pushing their contents on the link.
        for output in outputs.iter_mut() {
            let port_idx: usize = port.into();
            let _vcd_i_scope = callbacks
                .get_vcd_writer()
                .map(|writer| VcdWriter::managed_trace_scope(writer, &port_idx));
            self.gatherers[port_idx]
                .step(output, callbacks)
                .unwrap_or_else(|err| {
                    panic!(
                        "cycle {}: Failed receiving on port {} error {}",
                        self.local_cycles,
                        port_idx,
                        err.to_string()
                    )
                });
        }
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

        // Step the scatter memories, bringing the link's frame into rx memory.
        for input in inputs.iter() {
            let _vcd_port_scope = callbacks
                .get_vcd_writer()
                .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), &port));
            let port_idx: usize = port.into();
            self.scatterers[port_idx]
                .step(*input, callbacks)
                .unwrap_or_else(|_| {
                    panic!(
                        "cycle {}: Failed receiving on port {}",
                        self.local_cycles, port
                    )
                });
        }
        Ok(())
    }

    /// bookkeeping for advancing a node to the next metacycle.
    ///
    /// This includes, resetting the calendars and the read/write pointers
    /// into memory, and resetting the local local_cycle_counter (used to index
    /// calendars).
    fn advance_metacycle(&mut self) {
        assert!(self
            .crossbar_latency_queues
            .iter()
            .all(|q| q.iter().all(|e| e.is_none())));
        self.crossbar.advance_metacycle();
        for s in self.scatterers.iter_mut() {
            s.advance_metacycle();
        }

        for g in self.gatherers.iter_mut() {
            g.advance_metacycle();
        }
    }

    fn set_starting_cycles(&mut self, cycle: Cycle) {
        self.starting_cycles = cycle;
    }

    fn starting_cycles(&self) -> Cycle {
        self.starting_cycles
    }

    fn local_cycles(&self) -> Cycle {
        self.local_cycles + self.starting_cycles
    }

    fn set_mailbox(&mut self, _: MailBox) {
        unimplemented!("Switches have no mailboxes.");
    }

    fn get_mailbox(&self) -> Option<&MailBox> {
        unimplemented!("Switches have no mailboxes.");
    }

    fn set_crashed(&mut self, crashed: bool) {
        self.crashed = crashed;
    }

    fn get_crashed(&self) -> bool {
        self.crashed
    }
}

impl<const BUFFERING: Buffering> VcdComponent for SwitchNode<BUFFERING> {
    fn vcd_write_scope(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_name_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), self.name());
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
        self.crossbar.vcd_write_scope(Rc::clone(&writer));
        for queue_idx in 0..self.crossbar_latency {
            for (input_idx, scatter) in self.scatterers.iter().enumerate() {
                writer.borrow_mut().add_var(
                    vcd_ext::VarType::Reg,
                    scatter.frame_size(),
                    format!("\\delay[{}][{}]", input_idx, queue_idx).as_str(),
                    None,
                );
            }
        }
    }

    fn vcd_init(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_name_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), self.name());
        writer
            .borrow_mut()
            .change_vector_immediately("local_cycles", self.local_cycles as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("starting_cycles", self.starting_cycles as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("current_cycles", self.local_cycles() as u32);
        for (i, g) in self.gatherers.iter().enumerate() {
            let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
            g.vcd_init(Rc::clone(&writer));
        }
        for (i, s) in self.scatterers.iter().enumerate() {
            let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
            s.vcd_init(Rc::clone(&writer));
        }
        self.crossbar.vcd_init(Rc::clone(&writer));
    }
}

impl<const BUFFERING: Buffering> SwitchNode<BUFFERING> {
    pub fn from_config(name: &str, config: &SwitchConfiguration) -> Self {
        // Populate the scatter/gather calendars. These calendars round-robin on
        // their respective memories.
        let gatherers = (0..config.output_link_count)
            .map(|_| {
                let gather = GatherEngine::<BUFFERING>::new(
                    config.link_configuration.frame_size,
                    config.link_configuration.memory_size,
                    config.link_configuration.calendar_size,
                    IOConfig::SwitchIO,
                );
                gather
            })
            .collect::<Vec<_>>();
        let scatterers = (0..config.input_link_count)
            .map(|_| {
                let scatter = ScatterEngine::<BUFFERING>::new(
                    config.link_configuration.frame_size,
                    config.link_configuration.memory_size,
                    config.link_configuration.calendar_size,
                    IOConfig::SwitchIO,
                );
                scatter
            })
            .collect::<Vec<_>>();
        let crossbar_latency_queues =
            vec![VecDeque::from(vec![None; config.crossbar_latency]); config.input_link_count];
        Self {
            crossbar: Crossbar::<BUFFERING> {
                output_count: gatherers.len(),
                ..Default::default()
            },
            name: String::from(name),
            scatterers,
            gatherers,
            cycles_per_metacycle: [config.cycles_per_metacycle; BUFFERING],
            local_cycles: 0,
            starting_cycles: config.starting_cycles,
            frequency: Frequency::new(config.frequency),
            crossbar_latency: config.crossbar_latency,
            crossbar_latency_queues: crossbar_latency_queues,
            switch_type: SwitchType::Registered,
            crashed: false,
        }
    }
}

#[cfg(test)]
mod crossbar_tests {
    use super::*;
    use crate::{
        calendar::CrossbarCalendarEntry,
        error::Error,
        sim::SystemSimulationCallbacks,
        specs::{InputFrameRef, OutputFrameRef},
        DataWithValidity,
    };
    use bits::Bits;

    struct TestData {
        input_frames: Vec<Data>,
        output_frames: Vec<DataWithValidity>,
    }

    impl Default for TestData {
        fn default() -> Self {
            Self {
                input_frames: (0..=3)
                    .map(|i| u32::pack(&(i as u32)).into_boxed_bitslice())
                    .collect::<Vec<_>>(),
                output_frames: vec![
                    DataWithValidity {
                        data: Default::default(),
                        valid: false,
                    };
                    4
                ],
            }
        }
    }

    #[test]
    fn test_crossbar_invalid_calendar() {
        let mut test_data = TestData::default();
        let mut crossbar = Crossbar::<{ BUFFERING_DOUBLE }>::default();
        crossbar.calendar = [
            vec![CrossbarCalendarEntry {
                // Invalid Calendar; there are 4 crossbar outputs, but only 2
                // input_source elements in the crossbar calendar.
                input_source: Some(vec![0, 2]),
                frame_count: 1,
            }],
            vec![CrossbarCalendarEntry::new(None, 1)],
        ];
        let input_frame_refs = vec![
            Some(&test_data.input_frames[0]),
            Some(&test_data.input_frames[1]),
            Some(&test_data.input_frames[2]),
            Some(&test_data.input_frames[3]),
        ];
        let mut output_frame_refs = test_data.output_frames.iter_mut().collect::<Vec<_>>();
        let step_maybe = crossbar.step(
            &input_frame_refs,
            &mut output_frame_refs,
            &mut SystemSimulationCallbacks::default(),
        );
        assert_eq!(step_maybe.err(), Some(Error::InvalidCalendar));
    }

    #[test]
    fn test_crossbar_invalid_address() {
        let mut test_data = TestData::default();
        let input_frame_refs: Vec<InputFrameRef> = vec![
            Some(&test_data.input_frames[0]),
            Some(&test_data.input_frames[1]),
            Some(&test_data.input_frames[2]),
            Some(&test_data.input_frames[3]),
        ];
        let mut output_frame_refs: Vec<OutputFrameRef> =
            test_data.output_frames.iter_mut().collect::<Vec<_>>();
        let mut crossbar = Crossbar::default();
        crossbar.calendar = [
            vec![CrossbarCalendarEntry {
                // Invalid Address 10; there exist 4 input ports addressed 0..3.
                input_source: Some(vec![0, 10, 2, 3]),
                frame_count: 1,
            }],
            vec![CrossbarCalendarEntry::new(None, 1)],
        ];
        let step_maybe = crossbar.step(
            &input_frame_refs,
            &mut output_frame_refs,
            &mut SystemSimulationCallbacks::default(),
        );
        assert_eq!(step_maybe.err(), Some(Error::InvalidAddress));
    }

    #[test]
    fn test_crossbar_step() {
        // Setup inputs
        let input_frames: Vec<Data> = (0..=3)
            .map(|i| u32::pack(&(i as u32)).into_boxed_bitslice())
            .collect::<Vec<_>>();
        let input_frame_refs: Vec<InputFrameRef> = vec![
            Some(&input_frames[0]),
            Some(&input_frames[1]),
            None,
            Some(&input_frames[3]),
        ];
        // Setup outputs
        let mut output_frames: Vec<DataWithValidity> = vec![
            DataWithValidity {
                data: Default::default(),
                valid: false,
            };
            4
        ];
        let mut output_frame_refs: Vec<OutputFrameRef> =
            output_frames.iter_mut().collect::<Vec<_>>();
        let mut crossbar = Crossbar::<{ BUFFERING_DOUBLE }>::default();
        crossbar.calendar = [
            vec![
                CrossbarCalendarEntry {
                    input_source: Some(vec![0, 1, 2, 3]),
                    frame_count: 1,
                },
                CrossbarCalendarEntry {
                    input_source: None,
                    frame_count: 1,
                },
                CrossbarCalendarEntry {
                    input_source: Some(vec![3, 1, 0, 0]),
                    frame_count: 2,
                },
            ],
            vec![CrossbarCalendarEntry::new(None, 4)],
        ];
        // Test the crossbar, each time the crossbar is stepped the outputs are updated.

        // Step 1
        ////
        let step_ok = crossbar.step(
            &input_frame_refs,
            &mut output_frame_refs,
            &mut SystemSimulationCallbacks::default(),
        );
        assert!(step_ok.is_ok());
        assert_eq!(
            &output_frames,
            &vec![
                DataWithValidity {
                    data: input_frames[0].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: input_frames[1].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: Default::default(),
                    valid: false,
                },
                DataWithValidity {
                    data: input_frames[3].clone(),
                    valid: true,
                },
            ]
        );
        assert_eq!(crossbar.entry_ptr, 1);
        assert_eq!(crossbar.frame_count, 0);

        // Step 2
        ////
        let expected_output_frames = output_frames.clone();
        let mut output_frame_refs: Vec<OutputFrameRef> =
            output_frames.iter_mut().collect::<Vec<_>>();
        let step_ok = crossbar.step(
            &input_frame_refs,
            &mut output_frame_refs,
            &mut SystemSimulationCallbacks::default(),
        );
        assert!(step_ok.is_ok());
        assert_eq!(output_frames, expected_output_frames);
        assert_eq!(crossbar.entry_ptr, 2);
        assert_eq!(crossbar.frame_count, 0);

        // Step 3
        ////
        let mut output_frame_refs: Vec<OutputFrameRef> =
            output_frames.iter_mut().collect::<Vec<_>>();
        let step_ok = crossbar.step(
            &input_frame_refs,
            &mut output_frame_refs,
            &mut SystemSimulationCallbacks::default(),
        );
        assert!(step_ok.is_ok());
        assert_eq!(
            &output_frames,
            &vec![
                DataWithValidity {
                    data: input_frames[3].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: input_frames[1].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: input_frames[0].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: input_frames[0].clone(),
                    valid: true,
                },
            ]
        );

        assert_eq!(crossbar.entry_ptr, 2);
        assert_eq!(crossbar.frame_count, 1);

        // Step 4
        ////
        let mut output_frame_refs: Vec<OutputFrameRef> =
            output_frames.iter_mut().collect::<Vec<_>>();
        let step_ok = crossbar.step(
            &input_frame_refs,
            &mut output_frame_refs,
            &mut SystemSimulationCallbacks::default(),
        );
        assert!(step_ok.is_ok());
        assert_eq!(
            &output_frames,
            &vec![
                DataWithValidity {
                    data: input_frames[3].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: input_frames[1].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: input_frames[0].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: input_frames[0].clone(),
                    valid: true,
                },
            ]
        );

        // Our entry_ptr is now invalid. We've walked off the end of the
        // calendar. This should never happen in practice because
        // advance_metacycle should have been called already. The implementation
        // causes it to wrap around, so here we test that 3 % 3 == 0.
        assert_eq!(crossbar.entry_ptr, 0);
        assert_eq!(crossbar.frame_count, 0);

        // Step failure! Verify that we report an error if we walk off the
        // calendar by forcing the entry ptr to be outside range.
        crossbar.entry_ptr = 3;
        let mut output_frame_refs: Vec<OutputFrameRef> =
            output_frames.iter_mut().collect::<Vec<_>>();
        let step_ok = crossbar.step(
            &input_frame_refs,
            &mut output_frame_refs,
            &mut SystemSimulationCallbacks::default(),
        );
        assert_eq!(step_ok.err(), Some(Error::OutOfCalendar));
    }

    #[test]
    fn test_zero_latency_switch() {
        type FrameType = u32;
        let mut test_data = TestData::default();
        let input_frame_refs: Vec<InputFrameRef> = vec![
            Some(&test_data.input_frames[0]),
            Some(&test_data.input_frames[1]),
            Some(&test_data.input_frames[2]),
            Some(&test_data.input_frames[3]),
        ];
        let output_frame_refs: Vec<OutputFrameRef> =
            test_data.output_frames.iter_mut().collect::<Vec<_>>();
        let mut switch = SwitchNode::<{ BUFFERING_DOUBLE }>::from_config(
            "switch",
            &SwitchConfiguration {
                input_link_count: 4,
                output_link_count: 4,
                crossbar_latency: 0,
                link_configuration: LinkConfiguration {
                    frame_size: std::mem::size_of::<FrameType>() * 8,
                    ..Default::default()
                },
                ..Default::default()
            },
        );
        switch.set_calendar(CalendarVariant::Crossbar([
            vec![CrossbarCalendarEntry::new(Some(vec![3, 1, 2, 0]), 1)],
            vec![CrossbarCalendarEntry::new(None, 1)],
        ]));
        for port_idx in 0..4 {
            switch.into_mut_provisioned_node().unwrap().set_io_calendar(
                IOCalendarVariant::Input([
                    vec![CalendarEntry::new(Some(0), 1)],
                    vec![CalendarEntry::new(None, 1)],
                ]),
                Port::new_in(port_idx),
            );
            switch.into_mut_provisioned_node().unwrap().set_io_calendar(
                IOCalendarVariant::Output([
                    vec![CalendarEntry::new(Some(0), 1)],
                    vec![CalendarEntry::new(None, 1)],
                ]),
                Port::new_in(port_idx),
            );
        }
        let step_scatterers_ok = switch
            .scatterers
            .iter_mut()
            .zip(input_frame_refs)
            .map(|(scatter, input_frame_ref)| {
                let rv = scatter.step(input_frame_ref, &mut SystemSimulationCallbacks::default());
                scatter.debug_dump_memory();
                rv
            })
            .collect::<Result<Vec<_>, _>>();
        assert!(step_scatterers_ok.is_ok());
        let step_ok = switch.step(&[], &mut [], &mut SystemSimulationCallbacks::default());
        assert!(step_ok.is_ok());
        let step_gatherers_ok = switch
            .gatherers
            .iter_mut()
            .zip(output_frame_refs)
            .map(|(gather, output_ref)| {
                let rv = gather.step(output_ref, &mut SystemSimulationCallbacks::default());
                gather.debug_dump_memory();
                rv
            })
            .collect::<Result<Vec<_>, _>>();
        assert!(step_gatherers_ok.is_ok());
        assert_eq!(
            &test_data.output_frames,
            &vec![
                DataWithValidity {
                    data: test_data.input_frames[3].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: test_data.input_frames[1].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: test_data.input_frames[2].clone(),
                    valid: true,
                },
                DataWithValidity {
                    data: test_data.input_frames[0].clone(),
                    valid: true,
                },
            ]
        );
    }
}

#[cfg(test)]
mod sys_switch_test {
    use super::*;
    use crate::app::Application;
    use crate::app::Service;
    use crate::app::ServiceHandle;
    use crate::calendar::CrossbarCalendarEntry;
    use crate::calendar::NodeCalendarEntry;
    use crate::hw::config::LinkConfiguration;
    use crate::hw::config::NodeConfiguration;
    use crate::hw::config::SwitchConfiguration;
    use crate::hw::ComputeNode;
    use crate::hw::HardwareSpec;
    use crate::hw::LoopbackRef;
    use crate::hw::Node;
    use crate::hw::Port;
    use crate::mailbox::ConnectionAttrs;
    use crate::mailbox::MappedAttrs;
    use crate::scheduler::CommsHandle;
    use crate::sim::SystemSimulationCallbacks;
    use crate::specs::ApplicationNode;
    use crate::specs::FrequencyFactor;
    use crate::specs::StatefulNode;
    use crate::specs::SystemContext;
    use crate::specs::{InputFrameRef, OutputFrameRef};
    use crate::CalendarEntry;
    use crate::Direction;
    use bits::Bits;

    type MsgType = u32;
    type FrameType = u64;

    fn iota_action(
        state: LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        let state_bits = &mut state.unwrap_or_else(|| panic!(""));
        let state = <(u32, u32, u32)>::unpack(state_bits);
        let result_double = inputs[0].map(|bits| MsgType::unpack(bits));
        let result_triple = inputs[1].map(|bits| MsgType::unpack(bits));
        let next_iota = state.0 + 1;
        let next_state = (
            next_iota,
            state.1 + result_double.unwrap_or(0),
            state.2 + result_triple.unwrap_or(0),
        );
        log::debug!(
            "[node0] state: {:?}, input[0]: {:?}, input[1]: {:?} output[0]: {}, next_state: {:?}",
            state,
            result_double,
            result_triple,
            next_iota,
            next_state,
        );
        next_iota.pack_to(&mut outputs[0].data);
        outputs[0].valid = true;
        // Save the next state.
        next_state.pack_to(state_bits);
    }

    fn double_action(
        _state: LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        let n = inputs[0].map(|bits| MsgType::unpack(bits));
        let result = n.map(|n| 2 * n);
        log::debug!("[node1] input[0]: {:?}, output[0]: {:?}", n, result);
        // serialize the output
        if let Some(result_value) = result {
            result_value.pack_to(&mut outputs[0].data);
            outputs[0].valid = true;
        } else {
            outputs[0].valid = false;
        }
    }

    fn triple_action(
        _state: LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        let n = inputs[0].map(|bits| MsgType::unpack(bits));
        let result = n.map(|n| 3 * n);
        log::debug!("[node2] input[0]: {:?}, output[0]: {:?}", n, result);
        // serialize the output
        if let Some(result_value) = result {
            result_value.pack_to(&mut outputs[0].data);
            outputs[0].valid = true;
        } else {
            outputs[0].valid = false;
        }
    }

    #[test]
    fn test_switch_hw_topology() {
        let _logger = env_logger::builder().is_test(true).try_init();

        // Summary:
        //
        // iota: sends a sequence of numbers n: 0, 1, 2, 3, ... to nodes double/triple
        //   - state: (n, sum{double-results}, sum{triple-results})
        //
        // double: sends 2*n back to iota
        //
        // triple: sends 3*n back to iota
        //
        // Test objectives:
        //   - frame multicast in the switch (iota frame sent to both double & triple)
        //   - exercising multiple calendars in conjunction with the switch calendar
        //
        //               +--------+
        //               |        |      +--------+
        //               |     o:1|=====>|i:0     |
        //               |        |      | double |
        //               |     i:1|<-----|o:0     |
        //               |        |      +--------+
        //  +-------+    | switch |
        //  |    i:1|<---|o:1     |      +--------+
        //  |    i:0|<---|o:0  o:2|=====>|i:0     |
        //  | iota  |    |        |      | triple |
        //  |    o:0|===>|i:0  i:2|<-----|o:0     |
        //  +-------+    +--------+      +--------+
        //

        // create an application
        let mut app_spec = Application::new();
        const CYCLES_PER_METACYCLE: usize = 4;
        let iota_node = app_spec.add_node(Service::new(
            "iota",
            iota_action,
            Some(<(u32, u32, u32)>::pack(&(0, 0, 0)).into_boxed_bitslice()),
            FrequencyFactor(1),
        ));
        let double_node = app_spec.add_node(Service::new(
            "double",
            double_action,
            None,
            FrequencyFactor(1),
        ));
        let triple_node = app_spec.add_node(Service::new(
            "triple",
            triple_action,
            None,
            FrequencyFactor(1),
        ));
        let msg_size = std::mem::size_of::<MsgType>() * 8;
        // Needed to set msg sizes for service functions.
        for node in [double_node, triple_node] {
            app_spec
                .get_node(node)
                .as_ref()
                .borrow_mut()
                .set_ports_properties(&[
                    (
                        PortLabel::Number(0),
                        PortProperties {
                            frame_size: crate::FrameSize::Computed(RttiType::new::<MsgType>()),
                            direction: Direction::Incoming,
                            ..Default::default()
                        },
                    ),
                    (
                        PortLabel::Number(2),
                        PortProperties {
                            frame_size: crate::FrameSize::Computed(RttiType::new::<MsgType>()),
                            direction: Direction::Outgoing,
                            ..Default::default()
                        },
                    ),
                ]);
        }
        app_spec
            .get_node(iota_node)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[
                (
                    PortLabel::Number(0),
                    PortProperties {
                        frame_size: crate::FrameSize::Computed(RttiType::new::<MsgType>()),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(1),
                    PortProperties {
                        frame_size: crate::FrameSize::Computed(RttiType::new::<MsgType>()),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(2),
                    PortProperties {
                        frame_size: crate::FrameSize::Computed(RttiType::new::<MsgType>()),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                ),
            ]);

        // Hardware topology.
        let mut system_spec = HardwareSpec::new();
        // Build the nodes.
        let memory_size = std::mem::size_of::<MsgType>() / std::mem::size_of::<FrameType>()
            + usize::from(std::mem::size_of::<MsgType>() % std::mem::size_of::<FrameType>() != 0);
        let link_cfg = LinkConfiguration {
            frame_size: std::mem::size_of::<FrameType>() * 8,
            latency: 0,
            memory_size: memory_size,
            ..Default::default()
        };
        let node_cfg_iota = NodeConfiguration {
            frequency: 1,
            cycles_per_metacycle: CYCLES_PER_METACYCLE,
            input_links: vec![link_cfg, link_cfg],
            output_links: vec![link_cfg],
            ..Default::default()
        };
        // Subtlety: starting cycles are randomly generated, using the same config results in the same
        // starting cycle.
        let node_cfg_factory = || NodeConfiguration {
            frequency: 1,
            cycles_per_metacycle: CYCLES_PER_METACYCLE,
            input_links: vec![link_cfg],
            output_links: vec![link_cfg],
            ..Default::default()
        };
        let mailbox_mapped_attrs = MappedAttrs {
            base_address: Some(0),
            hw_io_index: Some(0),
            frame_size: link_cfg.frame_size,
            memory_size: link_cfg.memory_size,
        };
        let iota_mailboxes = MailBox {
            inboxes: vec![
                ConnectionAttrs {
                    connection_id: CommsHandle::new(app_spec.id(), EdgeIndex::from(0)), // bogus
                    message_size: msg_size,
                    service_io_index: 0,
                    service_name: String::from("iota"),
                    mapped_endpoint: Some(mailbox_mapped_attrs.clone()),
                },
                ConnectionAttrs {
                    connection_id: CommsHandle::new(app_spec.id(), EdgeIndex::from(0)), // bogus
                    message_size: msg_size,
                    service_io_index: 1,
                    service_name: String::from("iota"),
                    mapped_endpoint: Some(MappedAttrs {
                        hw_io_index: Some(1),
                        ..mailbox_mapped_attrs
                    }),
                },
            ],
            outboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), EdgeIndex::from(0)), // bogus
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("iota"),
                mapped_endpoint: Some(mailbox_mapped_attrs.clone()),
            }],
        };
        let iota_hw_node_id = system_spec.add_node(Node::ComputeNode(ComputeNode::from_config(
            "iota",
            &node_cfg_iota,
        )));
        system_spec
            .get_node(iota_hw_node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_mailbox(iota_mailboxes);

        let double_mailboxes = MailBox {
            inboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), EdgeIndex::from(0)), // bogus
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("double"),
                mapped_endpoint: Some(mailbox_mapped_attrs.clone()),
            }],
            outboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), EdgeIndex::from(0)), // bogus
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("double"),
                mapped_endpoint: Some(mailbox_mapped_attrs.clone()),
            }],
        };
        let double_hw_node_id = system_spec.add_node(Node::ComputeNode(ComputeNode::from_config(
            "double",
            &node_cfg_factory(),
        )));
        system_spec
            .get_node(double_hw_node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_mailbox(double_mailboxes);

        let triple_mailboxes = MailBox {
            inboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), EdgeIndex::from(0)), // bogus
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("triple"),
                mapped_endpoint: Some(mailbox_mapped_attrs.clone()),
            }],
            outboxes: vec![ConnectionAttrs {
                connection_id: CommsHandle::new(app_spec.id(), EdgeIndex::from(0)), // bogus
                message_size: msg_size,
                service_io_index: 0,
                service_name: String::from("triple"),
                mapped_endpoint: Some(mailbox_mapped_attrs.clone()),
            }],
        };
        let triple_hw_node_id = system_spec.add_node(Node::ComputeNode(ComputeNode::from_config(
            "triple",
            &node_cfg_factory(),
        )));
        system_spec
            .get_node(triple_hw_node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_mailbox(triple_mailboxes);

        // Build the switch.
        let switch_cfg = SwitchConfiguration {
            frequency: 1,
            cycles_per_metacycle: CYCLES_PER_METACYCLE,
            crossbar_latency: 2,
            input_link_count: 3,
            output_link_count: 4,
            link_configuration: LinkConfiguration {
                memory_size: 1,
                frame_size: std::mem::size_of::<FrameType>() * 8,
                ..Default::default()
            },
            ..Default::default()
        };
        let switch_node_id = system_spec.add_node(Node::SwitchNode(SwitchNode::from_config(
            "switch",
            &switch_cfg,
        )));
        // Connect via links.
        //
        // switch connectivity,
        //   input  0: iota
        //   input  1: double
        //   input  2: triple
        //
        //   output 0: iota
        //   output 1: iota
        //   output 2: double
        //   output 3: triple

        system_spec.link_simplex(
            iota_hw_node_id,
            switch_node_id,
            Link::from_config(0, 0, link_cfg),
        );
        system_spec.link_simplex(
            switch_node_id,
            iota_hw_node_id,
            Link::from_config(0, 0, link_cfg),
        );
        system_spec.link_simplex(
            switch_node_id,
            iota_hw_node_id,
            Link::from_config(1, 1, link_cfg),
        );
        system_spec.link_simplex(
            double_hw_node_id,
            switch_node_id,
            Link::from_config(0, 1, link_cfg),
        );
        system_spec.link_simplex(
            switch_node_id,
            double_hw_node_id,
            Link::from_config(2, 0, link_cfg),
        );
        system_spec.link_simplex(
            switch_node_id,
            triple_hw_node_id,
            Link::from_config(3, 0, link_cfg),
        );
        system_spec.link_simplex(
            triple_hw_node_id,
            switch_node_id,
            Link::from_config(0, 2, link_cfg),
        );

        let port_properties = PortProperties {
            frame_size: ports::FrameSize::Computed(RttiType::new::<FrameType>()),
            ..PortProperties::default()
        };
        // Setup iota node calendars.
        let iota_hw_node = system_spec.get_node(iota_hw_node_id);
        iota_hw_node.borrow_mut().register_app(
            ServiceHandle::new(app_spec.id(), iota_node),
            Rc::clone(&app_spec.get_node(iota_node)),
        );

        iota_hw_node
            .borrow_mut()
            .set_calendar(CalendarVariant::Node([
                vec![
                    NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE - 1),
                    NodeCalendarEntry::new(Some(ServiceHandle::new(app_spec.id(), iota_node)), 1),
                ],
                vec![NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE)],
            ]));
        iota_hw_node
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_io_calendar(
                IOCalendarVariant::Output([
                    vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                    vec![
                        CalendarEntry::new(Some(0), 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                    ],
                ]),
                Port::new(
                    0,
                    &PortProperties {
                        direction: Direction::Outgoing,
                        ..port_properties
                    },
                ),
            );
        iota_hw_node
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_io_calendar(
                IOCalendarVariant::Input([
                    vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                    vec![
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(Some(0), 1),
                    ],
                ]),
                Port::new(
                    0,
                    &PortProperties {
                        direction: Direction::Incoming,
                        ..port_properties
                    },
                ),
            );
        iota_hw_node
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_io_calendar(
                IOCalendarVariant::Input([
                    vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                    vec![
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(Some(0), 1),
                    ],
                ]),
                Port::new(
                    1,
                    &PortProperties {
                        direction: Direction::Incoming,
                        ..port_properties
                    },
                ),
            );

        // Set switch node's crossbar calendar.
        let switch_hw_node = system_spec.get_node(switch_node_id);
        switch_hw_node
            .borrow_mut()
            .set_calendar(CalendarVariant::Crossbar([
                vec![CrossbarCalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                vec![CrossbarCalendarEntry::new(
                    Some(vec![1, 2, 0, 0]),
                    CYCLES_PER_METACYCLE,
                )],
            ]));
        switch_hw_node
            .borrow_mut()
            .set_cycles_per_metacycle([CYCLES_PER_METACYCLE; 2]);
        for input_idx in 0..system_spec.get_input_links(switch_node_id).count() {
            switch_hw_node
                .borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_io_calendar(
                    IOCalendarVariant::Input([
                        vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                        vec![CalendarEntry::new(Some(0), 1); CYCLES_PER_METACYCLE],
                    ]),
                    Port::new_in(input_idx),
                );
        }
        for output_idx in 0..system_spec.get_output_links(switch_node_id).count() {
            switch_hw_node
                .borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_io_calendar(
                    IOCalendarVariant::Output([
                        vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                        vec![CalendarEntry::new(Some(0), 1); CYCLES_PER_METACYCLE],
                    ]),
                    Port::new_out(output_idx),
                );
        }

        // Setup double node calendars.
        let double_hw_node = system_spec.get_node(double_hw_node_id);
        double_hw_node.borrow_mut().register_app(
            ServiceHandle::new(app_spec.id(), double_node),
            Rc::clone(&app_spec.get_node(double_node)),
        );
        double_hw_node
            .borrow_mut()
            .set_calendar(CalendarVariant::Node([
                vec![
                    NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE - 1),
                    NodeCalendarEntry::new(Some(ServiceHandle::new(app_spec.id(), double_node)), 1),
                ],
                vec![NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE)],
            ]));
        double_hw_node
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_io_calendar(
                IOCalendarVariant::Output([
                    vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                    vec![
                        CalendarEntry::new(Some(0), 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                    ],
                ]),
                Port::new(
                    0,
                    &PortProperties {
                        direction: Direction::Outgoing,
                        ..port_properties
                    },
                ),
            );
        double_hw_node
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_io_calendar(
                IOCalendarVariant::Input([
                    vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                    vec![
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(Some(0), 1),
                    ],
                ]),
                Port::new(
                    0,
                    &PortProperties {
                        direction: Direction::Incoming,
                        ..port_properties
                    },
                ),
            );

        // Setup triple node calendars.
        let triple_hw_node = system_spec.get_node(triple_hw_node_id);
        triple_hw_node.borrow_mut().register_app(
            ServiceHandle::new(app_spec.id(), triple_node),
            Rc::clone(&app_spec.get_node(triple_node)),
        );
        triple_hw_node
            .borrow_mut()
            .set_calendar(CalendarVariant::Node([
                vec![
                    NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE - 1),
                    NodeCalendarEntry::new(Some(ServiceHandle::new(app_spec.id(), triple_node)), 1),
                ],
                vec![NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE)],
            ]));
        triple_hw_node
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_io_calendar(
                IOCalendarVariant::Output([
                    vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                    vec![
                        CalendarEntry::new(Some(0), 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                    ],
                ]),
                Port::new(
                    0,
                    &PortProperties {
                        direction: Direction::Outgoing,
                        ..port_properties
                    },
                ),
            );
        triple_hw_node
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_io_calendar(
                IOCalendarVariant::Input([
                    vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)],
                    vec![
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(None, 1),
                        CalendarEntry::new(Some(0), 1),
                    ],
                ]),
                Port::new(
                    0,
                    &PortProperties {
                        direction: Direction::Incoming,
                        ..port_properties
                    },
                ),
            );

        log::info!("system spec:\n{}", system_spec.to_graphviz());
        let mut simulation =
            HardwareSystemSimulation::new(&system_spec, FailureProperties::default());
        assert_eq!(
            [CYCLES_PER_METACYCLE, CYCLES_PER_METACYCLE],
            simulation.sim_cycles_per_metacycle(&system_spec)
        );
        let mut callbacks = SystemSimulationCallbacks::create_vcd_callbacks();
        callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::write_header(writer, &system_spec));

        //         0       1       2      3       4       5       6      7             ...
        // -------------------------------------------------------------------------
        //         x2      comms   x2     comms   x2      comms   x2     comms
        //         x3              x3             x3              x3
        //         iota            iota           iota            iota
        // -------------------------------------------------------------------------   ...
        // state:  0 (init)                               0 + 2          0 + 2 + 4
        //                                                0 + 3          0 + 3 + 4
        let cycles = 2 * (10 + 2) * CYCLES_PER_METACYCLE;
        for cycle in 0..=cycles {
            log::info!("cycle {}", cycle);
            simulation.simulate_system_one_cycle(&system_spec, &mut callbacks);
            if cycle % CYCLES_PER_METACYCLE == 0 {
                let iota_service = app_spec.get_node(iota_node);
                let iota_metacycle = iota_hw_node.borrow().metacycle();
                let iota_state =
                    <(u32, u32, u32)>::unpack(iota_service.borrow().persistent_state().unwrap());
                // The exact cycle (i.e., the loop index) depends on which cycle in the metacycle the action
                // function is evaluated, and so we test the value on the next metacycle to decouple this
                // dependency.
                //
                // E.g., we test expected value at metacycle 4 in metacycle 5.
                match iota_metacycle {
                    5 => {
                        assert_eq!(iota_state.1, 2 * (1));
                        assert_eq!(iota_state.2, 3 * (1));
                    }
                    7 => {
                        assert_eq!(iota_state.1, 2 * (1 + 2));
                        assert_eq!(iota_state.2, 3 * (1 + 2));
                    }
                    9 => {
                        assert_eq!(iota_state.1, 2 * (1 + 2 + 3));
                        assert_eq!(iota_state.2, 3 * (1 + 2 + 3));
                    }
                    11 => {
                        assert_eq!(iota_state.1, 2 * (1 + 2 + 3 + 4));
                        assert_eq!(iota_state.2, 3 * (1 + 2 + 3 + 4));
                    }
                    _ => (),
                };
            }
        }
        callbacks
            .get_vcd_writer()
            .map(|writer| writer.borrow_mut().flush_after_simulation());

        let iota_state = <(u32, u32, u32)>::unpack(
            app_spec
                .get_node(iota_node)
                .borrow()
                .persistent_state()
                .unwrap(),
        );
        assert_eq!(iota_state.1, 110);
        assert_eq!(iota_state.2, 165);
    }
}
