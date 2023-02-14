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

use crate::calendar::{Calendar, CalendarEntry, CalendarVariantRef, Frame, IOCalendarVariant};
use crate::sim::OptionSimCallbacks;
use crate::vcd::{ChangeValue, VcdComponent};
use crate::Error;
use ::vcd as vcd_ext;
use calendar::Buffering;
use hw::RunConfig;

/// An RxMemory represents the receiving end of a memory link.
///
/// It is a sequence of frames, just as they copied by the scatter engine
/// from the incoming link.
pub type RxMemory = Vec<Option<Frame>>;

/// ScatterEngine represents the receiving end of a link.
///
/// It consists of:
///   - a calendar driving the data flow
///   - a memory to receive the data
///   - a write pointer that provides the location in memory where the data
///   goes. This is part of the state of the engine, and it is updated based
///   on the calendar entry frame count value.
///   - a pointer to the calendar entry (similar to a PC). It is linearly
///   incremented, or reset to the beginning of the calendar on each new
///   metacycle.
#[derive(Clone, Debug)]
pub struct ScatterEngine<const BUFFERING: Buffering> {
    memory: [RxMemory; BUFFERING],
    calendar: [Calendar; BUFFERING],
    calendar_manager: CalendarManagement<BUFFERING>,
    /// "Running" implies respective memory used for communication I/O.
    run_config: RunConfig,
    io_config: IOConfig,
    link_status: LinkStatus,
}

#[derive(Clone, Debug)]
struct CalendarManagement<const BUFFERING: Buffering> {
    write_ptr: usize,
    entry_ptr: usize,
    /// The frame size - not known from Data type.
    frame_size: usize,
    require_advance_metacycle: bool,
}

pub struct MutScatterEngineComms<'a, const BUFFERING: Buffering> {
    comms_memory: &'a mut RxMemory,
    calendar: &'a Calendar,
    run_config: RunConfig,
    calendar_manager: &'a mut CalendarManagement<BUFFERING>,
    link_status: LinkStatus,
}

#[allow(dead_code)]
pub struct ScatterEngineCompute<'a, const BUFFERING: Buffering> {
    compute_memory: &'a RxMemory,
    calendar: &'a Calendar,
    run_config: RunConfig,
    calendar_manager: &'a CalendarManagement<BUFFERING>, // Needed later, dead_code at present.
}

impl<'a, const BUFFERING: Buffering> MutScatterEngineComms<'a, BUFFERING> {
    /// run the engine for a cycle.
    ///
    /// copy the data from the input to the memory, increment the write
    /// pointer, and (if needed) the entry index.
    pub fn step(
        &mut self,
        input: InputFrameRef,
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        if self.calendar_manager.require_advance_metacycle {
            return Err(Error::OutOfCalendar);
        }
        if self.calendar.is_empty() {
            return Err(Error::InvalidCalendar);
        }
        if let Some(input) = input {
            assert_eq!(input.as_bitslice().len(), self.calendar_manager.frame_size);
        }
        let calendar_entry = &self.calendar[self.calendar_manager.entry_ptr];
        let _vcd_scatter_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), "scatter"));
        callbacks.vcd(|writer| {
            let _vcd_calendar_scope =
                VcdWriter::managed_trace_scope(Rc::clone(&writer), "calendar");
            for buffer_idx in 0..BUFFERING {
                writer.borrow_mut().change_vector_immediately(
                    format!("base_address_{}", buffer_idx).as_str(),
                    calendar_entry.base_address,
                );
                writer.borrow_mut().change_vector_immediately(
                    format!("frame_count_{}", buffer_idx).as_str(),
                    calendar_entry.frame_count,
                );
            }
        });
        log::trace!("scatter: entry {:?}", calendar_entry);

        // copy the data frame into the rx_mem, whether there is data in the input frame or not.
        // This function does not do frame inspection, it is a simple copy operation.
        if let Some(base_addr) = calendar_entry.base_address {
            if (base_addr as usize) >= self.comms_memory.len() {
                return Err(Error::InvalidAddress);
            }

            let addr: usize = base_addr as usize + self.calendar_manager.write_ptr;
            if addr >= self.comms_memory.len() {
                return Err(Error::OutOfMemory);
            }

            // Copy received input into comms memory. If the link is down,
            // we fill the comms memory with invalid data, but still advance
            // our calendar.
            self.comms_memory[addr] = match self.link_status {
                LinkStatus::Up => input.cloned(),
                LinkStatus::Down => None,
            };
            let mem_name = match self.run_config {
                RunConfig::RunCalendar0 => "rx_mem_0",
                RunConfig::RunCalendar1 => "rx_mem_1",
            };
            let frame_ref = self.comms_memory[addr].as_ref();
            let frame_size = self.calendar_manager.frame_size;
            callbacks.vcd(|writer| {
                writer.borrow_mut().change_input_frame_ref(
                    format!("\\{}[{}]", mem_name, addr).as_str(),
                    frame_ref,
                    frame_size,
                    ChangeValue::Defer,
                );
            });
        }
        self.calendar_manager.write_ptr = if calendar_entry.frame_count != 0 {
            (self.calendar_manager.write_ptr + 1) % calendar_entry.frame_count as usize
        } else {
            0
        };
        if self.calendar_manager.write_ptr == 0 {
            // done with the current entry, move to the next one
            self.calendar_manager.entry_ptr =
                (self.calendar_manager.entry_ptr + 1) % self.calendar.len();
            self.calendar_manager.require_advance_metacycle = self.calendar_manager.entry_ptr == 0;
        }
        callbacks.vcd(|writer| {
            writer
                .borrow_mut()
                .change_vector("entry_ptr", self.calendar_manager.entry_ptr as u32);
            writer
                .borrow_mut()
                .change_vector("write_ptr", self.calendar_manager.write_ptr as u32);
        });
        Ok(())
    }
}

impl<const BUFFERING: Buffering> ScatterEngine<BUFFERING> {
    fn into_mut_comms(&mut self) -> MutScatterEngineComms<BUFFERING> {
        let active_comms_memory = self.active_comms_memory();
        let active_comms = self.active_comms();
        MutScatterEngineComms {
            comms_memory: &mut self.memory[active_comms_memory as usize],
            calendar: &self.calendar[active_comms.clone() as usize],
            calendar_manager: &mut self.calendar_manager,
            run_config: active_comms,
            link_status: self.link_status,
        }
    }

    fn active_comms(&self) -> RunConfig {
        match BUFFERING {
            BUFFERING_SINGLE => RunConfig::default(),
            BUFFERING_DOUBLE => self.run_config.clone(),
            _ => panic!("Unsupported buffering!"),
        }
    }

    fn active_compute(&self) -> RunConfig {
        match BUFFERING {
            BUFFERING_SINGLE => RunConfig::default(),
            BUFFERING_DOUBLE => self.run_config.toggle(),
            _ => panic!("Unsupported buffering!"),
        }
    }

    fn active_comms_memory(&self) -> RunConfig {
        match self.io_config {
            IOConfig::ComputeIO => self.active_comms(),
            IOConfig::SwitchIO => RunConfig::default(),
        }
    }

    fn active_compute_memory(&self) -> RunConfig {
        match self.io_config {
            IOConfig::ComputeIO => self.active_compute(),
            IOConfig::SwitchIO => RunConfig::default(),
        }
    }

    fn into_compute(&self) -> ScatterEngineCompute<BUFFERING> {
        ScatterEngineCompute {
            compute_memory: &self.memory[self.active_compute_memory() as usize],
            calendar: &self.calendar[self.active_compute() as usize],
            calendar_manager: &self.calendar_manager,
            run_config: self.active_compute(),
        }
    }

    /// Build an engine with the specified memory and calendar sizes.
    ///
    /// The engine is built in an "uninitialized" state: all calendar
    /// entries are set to do nothing, and the memory is all None.
    pub fn new(
        frame_size: usize,
        mem_capacity: usize,
        calendar_capacity: usize,
        io_config: IOConfig,
    ) -> Self {
        Self {
            memory: [(); BUFFERING].map(|_| vec![None; mem_capacity]),
            calendar: [(); BUFFERING].map(|_| vec![CalendarEntry::default(); calendar_capacity]),
            calendar_manager: CalendarManagement {
                write_ptr: 0,
                entry_ptr: 0,
                frame_size: frame_size,
                require_advance_metacycle: false,
            },
            run_config: RunConfig::default(),
            io_config: io_config,
            link_status: LinkStatus::Up,
        }
    }

    pub fn set_memory_size(&mut self, memory_size: usize) {
        self.memory = [(); BUFFERING].map(|_| vec![None; memory_size]);
    }

    pub fn step(
        &mut self,
        input: InputFrameRef,
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        self.into_mut_comms().step(input, callbacks)
    }

    /// reset the write pointer and the calendar entry pointer
    pub fn advance_metacycle(&mut self) {
        assert!(
            self.calendar_manager.require_advance_metacycle,
            "with state {:?}\n{:?}\n{:#?}\n{:?}",
            self.run_config, self.io_config, self.calendar, self.calendar_manager
        );
        self.reset_pointers();
        self.run_config = match BUFFERING {
            BUFFERING_DOUBLE => self.run_config.toggle(),
            BUFFERING_SINGLE => RunConfig::default(),
            _ => panic!(),
        };
        self.calendar_manager.require_advance_metacycle = false;
    }

    fn reset_pointers(&mut self) {
        self.calendar_manager.write_ptr = 0;
        self.calendar_manager.entry_ptr = 0;
    }

    pub fn force_advance_metacycle(&mut self) {
        self.reset_pointers();
        // TODO(cascaval): do we care about resetting the memory?
        // In the single app case, we don't.

        // TODO(izzard): We might need to do this if we want to switch apps
        // at metacycle boundaries.
        // Alternatively, we can partition the memory for application, and
        // in that case we need to implement some sort of address
        // translation so that we can isolate applications.

        // On a metacycle boundary double-buffered memories swap responsibilities.
        self.run_config = RunConfig::default();
        self.calendar_manager.require_advance_metacycle = false;
    }

    /// return the frame at the provided address
    pub fn memory(&self, address: usize) -> Option<&Data> {
        let scatter_compute = self.into_compute();
        assert!(address < scatter_compute.compute_memory.len());
        scatter_compute.compute_memory[address].as_ref()
    }

    /// set a new calendar
    ///
    // TODO(cascaval): While right now we only set this a single time when
    // we bootstrap an application, we'll need to implement updating
    // calendars "on the fly". That may require double buffering calendars
    // and atomically swapping from one to another.
    pub fn set_calendar(&mut self, calendar: IOCalendarVariant<BUFFERING>) {
        match calendar {
            IOCalendarVariant::Input(calendar) => self.calendar = calendar,
            _ => panic!("Illegal calendar assignment for scatter."),
        }
    }

    pub fn get_calendar(&self) -> Option<CalendarVariantRef<BUFFERING>> {
        Some(CalendarVariantRef::Input(&self.calendar))
    }

    pub fn memory_size(&self) -> usize {
        self.memory[0].len()
    }

    pub fn frame_size(&self) -> usize {
        self.calendar_manager.frame_size
    }

    pub fn set_link_status(&mut self, link_status: LinkStatus) {
        self.link_status = link_status;
    }

    pub fn get_link_status(&self) -> LinkStatus {
        self.link_status
    }

    pub fn debug_set_memory_0(&mut self, memory: &RxMemory) {
        self.memory[0] = memory.clone();
    }

    pub fn debug_set_memory_1(&mut self, memory: &RxMemory) {
        assert_eq!(BUFFERING, BUFFERING_DOUBLE);
        self.memory[1] = memory.clone();
    }

    pub fn debug_dump_memory(&self) {
        log::trace!(
            "entry_ptr: {}, write_ptr: {}, calendar: {:?}",
            self.calendar_manager.entry_ptr,
            self.calendar_manager.write_ptr,
            self.calendar[self.run_config.clone() as usize][self.calendar_manager.entry_ptr],
        );

        fn dump_memory(memory: &RxMemory) {
            if cfg!(feature = "trace-io-memory-contents") {
                for (i, entry) in memory.iter().enumerate() {
                    if let Some(contents) = entry {
                        log::trace!(
                            "{}: {:?}",
                            i,
                            contents
                                .iter()
                                .map(|b| (if *b { 1u32 } else { 0u32 }).to_string())
                                .collect::<String>()
                        );
                    }
                }
            }
        }
        match BUFFERING {
            BUFFERING_DOUBLE => {
                log::debug!(
                    "memory_0[{}] ({})",
                    self.memory_size(),
                    match self.run_config {
                        RunConfig::RunCalendar0 => "Comms",
                        RunConfig::RunCalendar1 => "Compute",
                    }
                );
                dump_memory(&self.memory[0]);
                log::debug!(
                    "memory_1[{}] ({})",
                    self.memory_size(),
                    match self.run_config {
                        RunConfig::RunCalendar1 => "Comms",
                        RunConfig::RunCalendar0 => "Compute",
                    }
                );
                dump_memory(&self.memory[1]);
            }
            BUFFERING_SINGLE => {
                log::debug!("memory_0[{}] (Comms+Compute)", self.memory_size());
                dump_memory(&self.memory[0]);
            }
            _ => panic!(),
        }
    }
}

impl<const BUFFERING: Buffering> VcdComponent for ScatterEngine<BUFFERING> {
    fn vcd_write_scope(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_scatter_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), "scatter");
        writer.borrow_mut().add_integer_var::<u32>("entry_ptr");
        writer.borrow_mut().add_integer_var::<u32>("write_ptr");
        for buffer in 0..BUFFERING {
            for addr in 0..self.memory_size() {
                writer.borrow_mut().add_var(
                    vcd_ext::VarType::Reg,
                    self.calendar_manager.frame_size,
                    format!("\\rx_mem_{}[{}]", buffer, addr).as_str(),
                    None,
                );
            }
        }
        {
            let _vcd_calendar_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), "calendar");
            for buffer_idx in 0..BUFFERING {
                writer
                    .borrow_mut()
                    .add_integer_var::<u32>(format!("base_address_{}", buffer_idx).as_str());
                writer
                    .borrow_mut()
                    .add_integer_var::<u32>(format!("frame_count_{}", buffer_idx).as_str());
            }
        }
    }

    fn vcd_init(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_scatter_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), "scatter");
        writer
            .borrow_mut()
            .change_vector_immediately("entry_ptr", self.calendar_manager.entry_ptr as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("write_ptr", self.calendar_manager.write_ptr as u32);
        {
            let _vcd_calendar_scope =
                VcdWriter::managed_trace_scope(Rc::clone(&writer), "calendar");
            for buffer_idx in 0..BUFFERING {
                let calendar = &self.calendar[buffer_idx][self.calendar_manager.entry_ptr];
                writer.borrow_mut().change_vector_immediately(
                    format!("base_address_{}", buffer_idx).as_str(),
                    calendar.base_address,
                );
                writer.borrow_mut().change_vector_immediately(
                    format!("frame_count_{}", buffer_idx).as_str(),
                    calendar.frame_count,
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::SystemSimulationCallbacks;
    use bits::Bits;
    use config::LinkConfiguration;

    #[test]
    fn test_scatter() {
        // verify the scatter engine
        //
        // check that the write pointer and calendar entry index are
        // incremented correctly based on a predefined calendar, that has 3
        // entries, one with 2 frames, 1 with 1 frame, an 1 with a None input.
        //
        // validate that the next calendar entry is also stored correctly,
        // and it wraps around, even on None entries.
        //
        // also validate that the rx_memory has the correct frames at the
        // end.

        // predefine a set of inputs
        let i0 = u32::pack(&0xcafebabe).into_boxed_bitslice();
        let i1 = u32::pack(&0xdeedbead).into_boxed_bitslice();
        let i2 = u32::pack(&0xfacefeed).into_boxed_bitslice();
        let i4 = u32::pack(&0xdeafbade).into_boxed_bitslice();
        let i5 = u32::pack(&0xdeaddead).into_boxed_bitslice();
        let inputs = vec![Some(&i0), Some(&i1), Some(&i2), None, Some(&i4), Some(&i5)];
        let config = LinkConfiguration {
            memory_size: 16,
            ..LinkConfiguration::default()
        };
        let mut scatter = ScatterEngine::<{ BUFFERING_DOUBLE }>::new(
            std::mem::size_of::<u32>() * 8,
            config.memory_size,
            config.calendar_size,
            IOConfig::ComputeIO,
        );

        // fill in some calendar entries
        let calendar = vec![
            CalendarEntry::new(Some(0), 2),
            CalendarEntry::new(Some(10), 1),
            CalendarEntry::new(Some(0), 1),
            CalendarEntry::default(),
            CalendarEntry::new(Some(5), 1),
        ];
        scatter.set_calendar(IOCalendarVariant::Input([
            calendar.clone(),
            calendar.clone(),
        ]));

        let memory_before_step = scatter.memory[0].clone();
        scatter
            .step(inputs[0], &mut SystemSimulationCallbacks::default())
            .expect("Failed cycle 0");
        // next frame is still on the current entry
        assert_eq!(scatter.calendar_manager.write_ptr, 1);

        scatter
            .step(inputs[1], &mut SystemSimulationCallbacks::default())
            .expect("Failed cycle 1");
        // next frame should go back at the begining of the base address,
        // and the engine should have moved to the next entry.
        assert_eq!(scatter.calendar_manager.write_ptr, 0);
        assert_eq!(scatter.calendar_manager.entry_ptr, 1);
        for i in 0..config.memory_size {
            match i {
                0 => assert_eq!(scatter.memory[0][0], Some(i0.clone())),
                1 => assert_eq!(scatter.memory[0][1], Some(i1.clone())),
                _ => assert_eq!(scatter.memory[0][i], memory_before_step[i]),
            }
        }
        let memory_before_step = scatter.memory[0].clone();
        scatter
            .step(inputs[2], &mut SystemSimulationCallbacks::default())
            .expect("Failed cycle 2");
        // next frame should go location 10, as the calendar entry base address is 10,
        // and the engine should have moved to the next entry.
        assert_eq!(scatter.calendar_manager.write_ptr, 0);
        assert_eq!(scatter.calendar_manager.entry_ptr, 2);
        for i in 0..config.memory_size {
            match i {
                10 => assert_eq!(scatter.memory[0][10], Some(i2.clone())),
                _ => assert_eq!(scatter.memory[0][i], memory_before_step[i]),
            }
        }

        // for this one we changed the base address, back to the beginning of the rx memory
        // so we should i3 (None) in slot 0.
        let memory_before_step = scatter.memory[0].clone();
        scatter
            .step(inputs[3], &mut SystemSimulationCallbacks::default())
            .expect("Failed cycle 3");
        assert_eq!(scatter.calendar_manager.write_ptr, 0);
        // and the engine should have moved to the next entry.
        assert_eq!(scatter.calendar_manager.entry_ptr, 3);
        for i in 0..config.memory_size {
            match i {
                0 => assert!(scatter.memory[0][0].is_none()),
                _ => assert_eq!(scatter.memory[0][i], memory_before_step[i]),
            }
        }

        // now we moved to an uninitialized calendar entry, so the memory
        // should stay unchanged, and only increment the entry pointer.
        let memory_before_step = scatter.memory[0].clone();
        scatter
            .step(inputs[4], &mut SystemSimulationCallbacks::default())
            .expect("Failed cycle 4");
        assert_eq!(scatter.calendar_manager.write_ptr, 0);
        assert_eq!(scatter.calendar_manager.entry_ptr, 4);
        assert!(scatter.memory[0][0].is_none());
        assert_eq!(*scatter.memory[0], memory_before_step);

        // and now, we reached another entry that writes at location 5.
        let memory_before_step = scatter.memory[0].clone();
        scatter
            .step(inputs[5], &mut SystemSimulationCallbacks::default())
            .expect("Failed cycle 5");
        assert_eq!(scatter.calendar_manager.write_ptr, 0);
        assert_eq!(scatter.calendar_manager.entry_ptr, 0); // 5 entries, entry_ptr wraps to 0
        assert!(scatter.memory[0][0].is_none());
        for i in 0..config.memory_size {
            match i {
                5 => assert_eq!(scatter.memory[0][5], Some(i5.clone())),
                _ => assert_eq!(scatter.memory[0][i], memory_before_step[i]),
            }
        }
    }

    #[test]
    fn test_scatter_oom() {
        let i0 = u32::pack(&0xcafebabe).into_boxed_bitslice();

        const RX_MEM_SIZE: usize = 2;
        const CAL_SIZE: usize = 2;
        let mut scatter = ScatterEngine::<{ BUFFERING_DOUBLE }>::new(
            std::mem::size_of::<u32>() * 8,
            RX_MEM_SIZE,
            CAL_SIZE,
            IOConfig::ComputeIO,
        );

        let mut calendar = vec![CalendarEntry::default(); CAL_SIZE];
        calendar[0] = CalendarEntry::new(Some(0), RX_MEM_SIZE + 2);
        calendar[1] = CalendarEntry::new(Some((RX_MEM_SIZE + 1) as u32), 1);
        scatter.set_calendar(IOCalendarVariant::Input([
            calendar.clone(),
            calendar.clone(),
        ]));

        // scatter to consume all the memory
        for _ in 0..RX_MEM_SIZE {
            let res = scatter.step(Some(&i0), &mut SystemSimulationCallbacks::default());
            assert!(res.is_ok());
        }
        // and one more -- should be outside the memory range
        let res = scatter.step(Some(&i0), &mut SystemSimulationCallbacks::default());
        assert_eq!(res.unwrap_err(), Error::OutOfMemory);

        // revert to a "sane entry"
        calendar[0] = CalendarEntry::new(Some(0), 1);
        scatter.set_calendar(IOCalendarVariant::Input([
            calendar.clone(),
            calendar.clone(),
        ]));
        scatter.force_advance_metacycle(); // and reset the pointers

        let res = scatter.step(Some(&i0), &mut SystemSimulationCallbacks::default());
        assert!(res.is_ok());
        // make sure we move to the next entry
        assert_eq!(scatter.calendar_manager.entry_ptr, 1);

        let res = scatter.step(Some(&i0), &mut SystemSimulationCallbacks::default());
        assert_eq!(res.unwrap_err(), Error::InvalidAddress);
    }
}
