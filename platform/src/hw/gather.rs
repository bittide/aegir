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
use ::vcd as vcd_ext;
use bitvec::prelude::BitVec;

use crate::calendar::Buffering;
use crate::calendar::{Calendar, CalendarEntry, CalendarVariantRef, IOCalendarVariant};
use crate::hw::RunConfig;
use crate::sim::OptionSimCallbacks;
use crate::vcd::ChangeValue;
use crate::Error;

/// A TxMemory represents the sending end of a memory link.
///
/// It is a sequence of data frames, tagged wether they are valid. The
/// gather engine will transform them into frames consumable on the input
/// side of the link.
pub type TxMemory = Vec<DataWithValidity>;

/// GatherEngine represents the sending end of a link.
///
/// It consists of:
///   - a calendar driving the data flow
///   - a memory to read the data from and send to the wire
///   - a read pointer that provides the location in memory to read the data.
///     The read pointer is part of the state of the engine, and it is
///     updated based on the calendar entry frame count value.
///   - a pointer to the calendar entry (similar to a PC). It is linearly
///     incremented, or reset to the beginning of the calendar on each new
///     metacycle.
#[derive(Clone, Debug)]
pub struct GatherEngine<const BUFFERING: Buffering> {
    memory: [TxMemory; BUFFERING],
    calendar: [Calendar; BUFFERING],
    calendar_manager: CalendarManagement,
    /// the frame size - not known from Data
    frame_size: usize,
    run_config: RunConfig,
    io_config: IOConfig,
    link_status: LinkStatus,
}

#[derive(Clone, Debug)]
struct CalendarManagement {
    read_ptr: usize,
    entry_ptr: usize,
    require_advance_metacycle: bool,
}

impl Default for CalendarManagement {
    fn default() -> Self {
        Self {
            read_ptr: 0,
            entry_ptr: 0,
            require_advance_metacycle: false,
        }
    }
}

pub struct MutGatherEngineComms<'a, const BUFFERING: Buffering> {
    comms_memory: &'a mut TxMemory,
    calendar: &'a Calendar,
    calendar_manager: &'a mut CalendarManagement,
    frame_size: usize,
    link_status: LinkStatus,
}

pub struct GatherEngineCompute<'a, const BUFFERING: Buffering> {
    compute_memory: &'a TxMemory,
    frame_size: usize,
    active_memory: RunConfig,
}

impl<'a, const BUFFERING: Buffering> GatherEngineCompute<'a, BUFFERING> {
    fn vcd_trace_write(&self, address: usize, writer: Rc<RefCell<VcdWriter>>) {
        // vcd_trace_write is used to trace the PE's write into the gather memory, the memory used
        // by the PE for this write isn't being used for comms.
        let mem_name = match self.active_memory {
            RunConfig::RunCalendar0 => "tx_mem_1",
            RunConfig::RunCalendar1 => "tx_mem_0",
        };
        let _vcd_gather_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), "gather");
        let frame_ref = &self.compute_memory[address];
        writer.borrow_mut().change_output_frame_ref(
            format!("\\{}[{}]", mem_name, address).as_str(),
            frame_ref,
            self.frame_size,
            ChangeValue::Defer,
        );
    }
}

impl<'a, const BUFFERING: Buffering> MutGatherEngineComms<'a, BUFFERING> {
    /// run the engine for a cycle.
    ///
    /// Takes a single frame from the memory and copies it to the wire. Then
    /// increments the read pointer, and (if needed) the entry index.
    fn step(&mut self, output: OutputFrameRef, callbacks: OptionSimCallbacks) -> Result<(), Error> {
        if self.calendar_manager.require_advance_metacycle {
            return Err(Error::OutOfCalendar);
        }
        if self.calendar.is_empty() {
            return Err(Error::InvalidCalendar);
        }
        let calendar_entry = &self.calendar[self.calendar_manager.entry_ptr];
        let _vcd_gather_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(Rc::clone(&writer), "gather"));
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
        log::trace!(
            "gather: entry {:?}, read_ptr {:?}",
            calendar_entry,
            self.calendar_manager.read_ptr
        );

        // If we have a calendar entry, and the link is up, transmit that data.
        if calendar_entry.base_address.is_some() && self.link_status == LinkStatus::Up {
            let base_addr = calendar_entry.base_address.unwrap() as usize;
            if base_addr >= self.comms_memory.len() {
                return Err(Error::InvalidAddress);
            }

            let addr: usize = base_addr + self.calendar_manager.read_ptr;
            if addr >= self.comms_memory.len() {
                return Err(Error::OutOfMemory);
            }

            // copy the data frame into the wire
            *output = DataWithValidity {
                data: self.comms_memory[addr].data.clone(),
                valid: self.comms_memory[addr].valid,
            };
        } else {
            *output = DataWithValidity {
                data: BitVec::repeat(false, self.frame_size).into_boxed_bitslice(),
                valid: false,
            }
        }
        // and increment the read pointer
        self.calendar_manager.read_ptr = if calendar_entry.frame_count != 0 {
            (self.calendar_manager.read_ptr + 1) % calendar_entry.frame_count as usize
        } else {
            0
        };
        if self.calendar_manager.read_ptr == 0 {
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
                .change_vector("read_ptr", self.calendar_manager.read_ptr as u32);
        });
        Ok(())
    }
}

impl<const BUFFERING: Buffering> GatherEngine<BUFFERING> {
    /// Returns the run config for which comms are performed. E.g., if RunConfig:RunCalendar0
    /// is returned this implies calendar 0 is used for comms.
    fn active_comms(&self) -> RunConfig {
        match BUFFERING {
            BUFFERING_SINGLE => RunConfig::default(),
            BUFFERING_DOUBLE => self.run_config.clone(),
            _ => panic!("Unsupported buffering!"),
        }
    }

    /// Returns the memory buffer used for I/O. Switches only use a single memory buffer
    /// but can have two calendars.
    fn active_comms_memory(&self) -> RunConfig {
        match self.io_config {
            IOConfig::ComputeIO => self.active_comms(),
            IOConfig::SwitchIO => RunConfig::default(),
        }
    }

    /// Similarly for active_comms_memory, returns the memory buffer accessed by compute.
    fn active_compute_memory(&self) -> RunConfig {
        match self.io_config {
            IOConfig::ComputeIO => match BUFFERING {
                BUFFERING_SINGLE => RunConfig::default(),
                BUFFERING_DOUBLE => self.run_config.toggle(),
                _ => panic!("Unsupported buffering!"),
            },
            IOConfig::SwitchIO => RunConfig::default(),
        }
    }

    fn into_mut_comms(&mut self) -> MutGatherEngineComms<BUFFERING> {
        let active_comms = self.active_comms();
        let active_comms_memory = self.active_comms_memory();
        MutGatherEngineComms {
            comms_memory: &mut self.memory[active_comms_memory as usize],
            calendar: &self.calendar[active_comms as usize],
            calendar_manager: &mut self.calendar_manager,
            frame_size: self.frame_size,
            link_status: self.link_status,
        }
    }

    fn into_compute(&self) -> GatherEngineCompute<BUFFERING> {
        GatherEngineCompute {
            compute_memory: &self.memory[self.active_compute_memory() as usize],
            active_memory: self.active_compute_memory(),
            frame_size: self.frame_size,
        }
    }

    /// Build an engine with the specified memory and calendar sizes.
    ///
    /// The engine is built in an "uninitialized" state: all calendar
    /// entries are set to do nothing, and the memory is all set to invalid.
    pub fn new(
        frame_size: usize,
        mem_capacity: usize,
        calendar_capacity: usize,
        io_config: IOConfig,
    ) -> Self {
        Self {
            memory: [(); BUFFERING].map(|_| {
                (0..mem_capacity)
                    .map(|_| DataWithValidity {
                        data: BitVec::repeat(false, frame_size).into_boxed_bitslice(),
                        valid: false,
                    })
                    .collect::<Vec<_>>()
            }),
            calendar: [(); BUFFERING].map(|_| vec![CalendarEntry::default(); calendar_capacity]),
            calendar_manager: CalendarManagement::default(),
            run_config: RunConfig::default(),
            frame_size: frame_size,
            io_config: io_config,
            link_status: LinkStatus::Up,
        }
    }

    pub fn set_memory_size(&mut self, memory_size: usize) {
        self.memory = [(); BUFFERING].map(|_| {
            (0..memory_size)
                .map(|_| DataWithValidity {
                    data: BitVec::repeat(false, self.frame_size()).into_boxed_bitslice(),
                    valid: false,
                })
                .collect::<Vec<_>>()
        });
    }

    pub fn step(
        &mut self,
        output: OutputFrameRef,
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        self.into_mut_comms().step(output, callbacks)
    }

    pub fn vcd_trace_write(&self, address: usize, writer: Rc<RefCell<VcdWriter>>) {
        self.into_compute().vcd_trace_write(address, writer)
    }

    /// Try to advance the metacycle, if the unit hasn't exhausted it's calendar then noop.
    pub fn advance_metacycle(&mut self) {
        assert!(self.calendar_manager.require_advance_metacycle);
        self.calendar_manager = CalendarManagement::default();
        self.run_config = match BUFFERING {
            BUFFERING_DOUBLE => self.run_config.toggle(),
            BUFFERING_SINGLE => RunConfig::default(),
            _ => panic!(),
        };
        self.calendar_manager.require_advance_metacycle = false;
    }

    /// reset the write pointer and the calendar entry pointer
    pub fn force_advance_metacycle(&mut self) {
        self.calendar_manager = CalendarManagement::default();
        // TODO(cascaval): do we care about resetting the memory?

        // Since this is write only, on the node side, do we even care?
        // TODO(izzard): Maybe, since another app can install calendar
        // entries that exfiltrate the data. Partitioning may help here as
        // well, just as in the case of scatter.
        self.run_config = RunConfig::default();
    }

    /// return the slice of memory that is to be filled by the application.
    pub fn memory(&mut self, address: usize) -> &mut DataWithValidity {
        assert!(address < self.memory_size());
        &mut self.memory[self.active_compute_memory() as usize][address]
    }

    /// set a new calendar
    ///
    // TODO(cascaval): While right now we only set this a single time when
    // we bootstrap an application, we'll need to implement updating
    // calendars "on the fly". That may require double buffering calendars
    // and atomically swapping from one to another.
    pub fn set_calendar(&mut self, calendar: IOCalendarVariant<BUFFERING>) {
        match calendar {
            IOCalendarVariant::Output(calendar) => self.calendar = calendar,
            _ => panic!("Illegal calendar assignment."),
        }
    }

    pub fn get_calendar(&self) -> Option<CalendarVariantRef<BUFFERING>> {
        Some(CalendarVariantRef::Output(&self.calendar))
    }

    pub fn memory_size(&self) -> usize {
        self.memory[0].len()
    }

    pub fn frame_size(&self) -> usize {
        self.frame_size
    }

    pub fn set_link_status(&mut self, link_status: LinkStatus) {
        self.link_status = link_status;
    }

    pub fn get_link_status(&self) -> LinkStatus {
        self.link_status
    }

    pub fn debug_dump_memory(&self) {
        fn dump_memory(memory: &TxMemory) {
            if cfg!(feature = "trace-io-memory-contents") {
                for (i, entry) in memory.iter().enumerate() {
                    if entry.valid {
                        log::trace!(
                            "{}: {:?}",
                            i,
                            entry
                                .data
                                .iter()
                                .map(|b| (if *b { 1u32 } else { 0u32 }).to_string())
                                .collect::<String>(),
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
                        RunConfig::RunCalendar0 => "Compute",
                        RunConfig::RunCalendar1 => "Comms",
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

    pub fn debug_get_memory_0(&mut self) -> TxMemory {
        self.memory[0].clone()
    }

    pub fn debug_get_memory_1(&mut self) -> TxMemory {
        assert_eq!(BUFFERING, BUFFERING_DOUBLE);
        self.memory[1].clone()
    }
}

impl<const BUFFERING: Buffering> VcdComponent for GatherEngine<BUFFERING> {
    fn vcd_write_scope(&self, writer: Rc<RefCell<VcdWriter>>) {
        let _vcd_gather_scope = VcdWriter::managed_decl_scope(Rc::clone(&writer), "gather");
        writer.borrow_mut().add_integer_var::<u32>("entry_ptr");
        writer.borrow_mut().add_integer_var::<u32>("read_ptr");
        for buffer_idx in 0..BUFFERING {
            for addr in 0..self.memory_size() {
                writer.borrow_mut().add_var(
                    vcd_ext::VarType::Reg,
                    self.frame_size,
                    format!("\\tx_mem_{}[{}]", buffer_idx, addr).as_str(),
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
        let _vcd_gather_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), "gather");
        writer
            .borrow_mut()
            .change_vector_immediately("entry_ptr", self.calendar_manager.entry_ptr as u32);
        writer
            .borrow_mut()
            .change_vector_immediately("   read_ptr", self.calendar_manager.read_ptr as u32);
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

    #[test]
    fn test_gather() {
        let mut output = DataWithValidity {
            data: u32::pack(&0xdeadbeef).into_boxed_bitslice(),
            valid: true,
        };
        let d0 = u32::pack(&0xbabeface).into_boxed_bitslice();
        let d1 = u32::pack(&0xcafebabe).into_boxed_bitslice();
        let d2 = u32::pack(&0xdeafbade).into_boxed_bitslice();

        const TX_MEM_SIZE: usize = 4;
        const CAL_SIZE: usize = 3;
        let mut engine = GatherEngine::<{ BUFFERING_DOUBLE }>::new(
            std::mem::size_of::<u32>() * 8,
            TX_MEM_SIZE,
            CAL_SIZE,
            IOConfig::ComputeIO,
        );
        engine.memory[0][0] = DataWithValidity {
            data: d0.clone(),
            valid: true,
        };
        engine.memory[0][1] = DataWithValidity {
            data: d1.clone(),
            valid: true,
        };
        engine.memory[0][3] = DataWithValidity {
            data: d2.clone(),
            valid: true,
        };

        let calendar_contents = vec![
            CalendarEntry::new(Some(0), 2),
            CalendarEntry::new(Some(3), 1),
            CalendarEntry::new(Some(2), 1),
        ];
        let calendar = [calendar_contents.clone(), calendar_contents];
        assert_eq!(calendar[0].len(), CAL_SIZE);
        engine.set_calendar(IOCalendarVariant::Output(calendar));

        let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
        assert!(res.is_ok());
        assert!(output.valid);
        assert_eq!(output.data, d0);
        assert_eq!(engine.calendar_manager.entry_ptr, 0);
        assert_eq!(engine.calendar_manager.read_ptr, 1);

        let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
        assert!(res.is_ok());
        assert!(output.valid);
        assert_eq!(output.data, d1);
        assert_eq!(engine.calendar_manager.entry_ptr, 1);
        assert_eq!(engine.calendar_manager.read_ptr, 0);

        let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
        assert!(res.is_ok());
        assert!(output.valid);
        assert_eq!(output.data, d2);
        assert_eq!(engine.calendar_manager.entry_ptr, 2);
        assert_eq!(engine.calendar_manager.read_ptr, 0);

        let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
        assert!(res.is_ok());
        assert_eq!(output.valid, false);
        // check that the calendar pointer has wrapped around.
        assert_eq!(engine.calendar_manager.entry_ptr, 0);
        assert_eq!(engine.calendar_manager.read_ptr, 0);

        // now run a bit more to test that the metacycle resets the pointers
        engine.advance_metacycle();
        assert_eq!(engine.run_config, RunConfig::RunCalendar1);
        for _ in 0..2 {
            let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
            assert!(res.is_ok());
        }
        assert_eq!(engine.calendar_manager.entry_ptr, 1);
        assert_eq!(engine.calendar_manager.read_ptr, 0);
        engine.force_advance_metacycle();
        assert_eq!(engine.run_config, RunConfig::RunCalendar0);
        assert_eq!(engine.calendar_manager.entry_ptr, 0);
        assert_eq!(engine.calendar_manager.read_ptr, 0);
    }

    #[test]
    fn test_gather_oom() {
        let mut output = DataWithValidity {
            data: u32::pack(&0xdeadbeef).into_boxed_bitslice(),
            valid: true,
        };

        const TX_MEM_SIZE: usize = 2;
        const CAL_SIZE: usize = 2;
        let mut engine = GatherEngine::<{ BUFFERING_DOUBLE }>::new(
            std::mem::size_of::<u32>() * 8,
            TX_MEM_SIZE,
            CAL_SIZE,
            IOConfig::ComputeIO,
        );

        let mut calendar_contents = vec![
            CalendarEntry::new(Some(0), TX_MEM_SIZE + 2),
            CalendarEntry::new(Some((TX_MEM_SIZE + 1) as u32), 1),
        ];
        assert_eq!(calendar_contents.len(), CAL_SIZE);
        engine.set_calendar(IOCalendarVariant::Output([
            calendar_contents.clone(),
            calendar_contents.clone(),
        ]));

        // run to consume all the memory
        for _ in 0..TX_MEM_SIZE {
            let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
            assert!(res.is_ok());
        }
        // and one more -- should be outside the memory range
        let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
        assert_eq!(res.unwrap_err(), Error::OutOfMemory);

        // revert to a "sane entry"
        calendar_contents[0] = CalendarEntry::new(Some(0), 1);
        engine.set_calendar(IOCalendarVariant::Output([
            calendar_contents.clone(),
            calendar_contents.clone(),
        ]));
        engine.force_advance_metacycle(); // and reset the pointers

        let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
        assert!(res.is_ok());
        // make sure we move to the next entry
        assert_eq!(engine.calendar_manager.entry_ptr, 1);

        let res = engine.step(&mut output, &mut SystemSimulationCallbacks::default());
        assert_eq!(res.unwrap_err(), Error::InvalidAddress);
    }
}
