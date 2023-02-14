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

use itertools::Itertools;

use super::*;
use crate::app::ServiceHandle;
use crate::Cycle;
use std::collections::HashMap;

/// `Frame` is a fixed-sized chunk that specifies the link connections
pub type Frame = Data;

pub trait CalendarEntrySpec<P: Eq + Clone> {
    fn noop(frame_count: usize) -> Self;
    fn payload(&self) -> Option<&P>;
    fn increment(&mut self, delta: u32);
    fn len(&self) -> u32;
}

pub fn calendar_depth<C: CalendarEntrySpec<P>, P: PartialEq + Eq + Clone>(
    calendar: &Vec<C>,
) -> Cycle {
    calendar.iter().map(|entry| entry.len() as usize).sum()
}

/// Generic algorithm to lower a sparse calendar to a compact representation
/// defined by the calendar encoding semantics.
///
/// A sparse calendar is a hashmap of cycles to calendar entries, i.e.,
/// HashMap<Cycle, C>.
pub trait CalendarSpec<C: CalendarEntrySpec<P> + Clone, P: PartialEq + Eq + Clone> {
    fn compact(sparse_calendar: &HashMap<Cycle, C>, start_time: Cycle) -> Vec<C> {
        let mut next_empty_cycle = start_time;
        let mut calendar: Vec<C> = vec![];
        let sorted_calendar = sparse_calendar
            .iter()
            .sorted_by_key(|item| item.0)
            .collect::<Vec<_>>();
        for (cycle, action) in sorted_calendar {
            let cycle = *cycle;
            assert!(cycle >= next_empty_cycle);
            if calendar.is_empty() {
                if cycle > next_empty_cycle {
                    calendar.push(C::noop(cycle - next_empty_cycle));
                }
                calendar.push(action.clone());
            } else {
                if cycle > next_empty_cycle {
                    let last_entry = calendar.last_mut().unwrap();
                    if last_entry.payload().is_none() {
                        last_entry.increment((cycle - next_empty_cycle) as u32);
                    } else {
                        calendar.push(C::noop(cycle - next_empty_cycle));
                    }
                }
                let last_entry = calendar.last_mut().unwrap();
                if action.payload() == last_entry.payload() {
                    last_entry.increment(action.len());
                } else {
                    calendar.push(action.clone());
                }
            }
            next_empty_cycle = cycle + action.len() as usize;
        }
        calendar
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CrossbarCalendarEntry {
    /// Defines the permutation of the crossbar switch. The crossbar has
    /// OUT_COUNT output ports, where the i'th port's input is sourced from
    /// source[i].
    ///
    /// Example: CrossbarCalendarEntry<4> has source: [u32; 4]. When source is
    /// [0, 1, 3, 2] that implies input 0 is routed to output 0, i.e., 0 -> 0.
    /// And similarly, 1 -> 1, 3 -> 2, 2 -> 3.
    pub input_source: Option<Vec<u32>>,

    /// defines the number of frames handled by this calendar entry.
    pub frame_count: u32,
}

impl CrossbarCalendarEntry {
    pub fn new(input_source: Option<Vec<u32>>, frame_count: usize) -> Self {
        Self {
            input_source: input_source.clone(),
            frame_count: frame_count as u32,
        }
    }
}

impl CalendarEntrySpec<Vec<u32>> for CrossbarCalendarEntry {
    fn noop(frame_count: usize) -> Self {
        Self {
            input_source: None,
            frame_count: frame_count as u32,
        }
    }

    fn increment(&mut self, delta: u32) {
        self.frame_count += delta as u32;
    }

    fn payload(&self) -> Option<&Vec<u32>> {
        self.input_source.as_ref()
    }

    fn len(&self) -> u32 {
        self.frame_count
    }
}

impl CalendarSpec<CrossbarCalendarEntry, Vec<u32>> for CrossbarCalendar {}

pub type CrossbarCalendar = Vec<CrossbarCalendarEntry>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CalendarEntry {
    /// defines the base address for the scatter/gather to write/read memory.
    pub base_address: Option<u32>,

    /// defines the number of frames handled by this calendar entry.
    pub frame_count: u32,
}

impl CalendarEntry {
    pub fn new(base_address: Option<u32>, frame_count: usize) -> Self {
        assert!(frame_count > 0);
        Self {
            base_address,
            frame_count: frame_count as u32,
        }
    }
}

impl CalendarEntrySpec<u32> for CalendarEntry {
    fn noop(frame_count: usize) -> Self {
        Self {
            base_address: None,
            frame_count: frame_count as u32,
        }
    }

    fn increment(&mut self, delta: u32) {
        self.frame_count += delta;
    }

    fn payload(&self) -> Option<&u32> {
        self.base_address.as_ref()
    }

    fn len(&self) -> u32 {
        self.frame_count
    }
}

/// Calendar compaction is algorithmically different because of how addresses
/// are computed via the scatter/gather calendar semantics.
impl CalendarSpec<CalendarEntry, u32> for Calendar {
    fn compact(sparse_calendar: &HashMap<Cycle, CalendarEntry>, start_time: Cycle) -> Calendar {
        let mut next_empty_cycle = start_time;
        let mut calendar = vec![];
        let sorted_calendar = sparse_calendar
            .iter()
            .sorted_by_key(|item| item.0)
            .collect::<Vec<_>>();
        for (cycle, action) in sorted_calendar {
            let cycle = *cycle;
            assert!(cycle >= next_empty_cycle);
            if calendar.is_empty() {
                if cycle > next_empty_cycle {
                    calendar.push(CalendarEntry::noop(cycle - next_empty_cycle));
                }
                calendar.push(action.clone());
            } else {
                if cycle > next_empty_cycle {
                    let last_entry = calendar.last_mut().unwrap();
                    if last_entry.payload().is_none() {
                        last_entry.increment((cycle - next_empty_cycle) as u32);
                    } else {
                        calendar.push(CalendarEntry::noop(cycle - next_empty_cycle));
                    }
                }
                let last_entry = calendar.last_mut().unwrap();
                if action.base_address
                    == last_entry
                        .base_address
                        .map(|last_base_address| last_base_address + last_entry.frame_count)
                {
                    last_entry.increment(action.frame_count);
                } else {
                    calendar.push(action.clone());
                }
            }
            next_empty_cycle = cycle + action.frame_count as usize;
        }
        calendar
    }
}

/// Calendar representation: a sequence of calendar entries.
pub type Calendar = Vec<CalendarEntry>;

impl Default for CalendarEntry {
    fn default() -> Self {
        Self::new(None, 1)
    }
}

/// Node calendars specify the compute cycles (duration) that a service uses at
/// a compute node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeCalendarEntry {
    // The node index of the service to be run in the Application.
    pub service_handle: Option<ServiceHandle>,

    // Number of cycles to run the service.
    pub duration: u32,
}

impl NodeCalendarEntry {
    pub fn new(service_handle: Option<ServiceHandle>, duration: usize) -> Self {
        assert!(duration > 0);
        Self {
            service_handle,
            duration: duration as u32,
        }
    }
}

impl Default for NodeCalendarEntry {
    fn default() -> Self {
        Self::new(None, 1)
    }
}

impl CalendarSpec<NodeCalendarEntry, ServiceHandle> for NodeCalendar {}

impl CalendarEntrySpec<ServiceHandle> for NodeCalendarEntry {
    fn noop(duration: usize) -> Self {
        Self {
            service_handle: None,
            duration: duration as u32,
        }
    }

    fn increment(&mut self, delta: u32) {
        self.duration += delta;
    }

    fn payload(&self) -> Option<&ServiceHandle> {
        self.service_handle.as_ref()
    }

    fn len(&self) -> u32 {
        self.duration
    }
}

/// NodeCalendar representation: a sequence of node calendar entries.
pub type NodeCalendar = Vec<NodeCalendarEntry>;

// TODO(pouyad) change to enum when the feature becomes stable.
pub type Buffering = usize;
pub const BUFFERING_SINGLE: usize = 1;
pub const BUFFERING_DOUBLE: usize = 2;
pub const APPLICATION_NODE: usize = 3;

/// Calendar variants used throughout aegir.
#[derive(Clone, Debug)]
pub enum IOCalendarVariant<const N: Buffering> {
    Output([Calendar; N]),
    Input([Calendar; N]),
}

/// Calendar variants used throughout aegir.
#[derive(Debug)]
pub enum CalendarVariant<const N: Buffering> {
    Crossbar([CrossbarCalendar; N]),
    Node([NodeCalendar; N]),
}

#[derive(Debug)]
pub enum CalendarVariantRef<'a, const N: Buffering> {
    Output(&'a [Calendar; N]),
    Input(&'a [Calendar; N]),
    Crossbar(&'a [CrossbarCalendar; N]),
    Node(&'a [NodeCalendar; N]),
}

#[cfg(test)]
mod calendar_tests {
    use super::CrossbarCalendarEntry;
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_crossbar_compaction() {
        let sparse = HashMap::<usize, _>::from([
            (111, CrossbarCalendarEntry::new(Some(vec![0, 1, 2, 3]), 1)),
            (112, CrossbarCalendarEntry::new(Some(vec![0, 1, 2, 3]), 2)),
            (115, CrossbarCalendarEntry::new(Some(vec![0, 1, 2, 3]), 1)),
            (116, CrossbarCalendarEntry::new(Some(vec![3, 2, 1, 0]), 1)),
            (117, CrossbarCalendarEntry::new(Some(vec![3, 2, 1, 0]), 1)),
        ]);
        assert_eq!(
            CrossbarCalendar::compact(&sparse, 80),
            vec![
                CrossbarCalendarEntry::new(None, 31),
                CrossbarCalendarEntry::new(Some(vec![0, 1, 2, 3]), 3),
                CrossbarCalendarEntry::new(None, 1),
                CrossbarCalendarEntry::new(Some(vec![0, 1, 2, 3]), 1),
                CrossbarCalendarEntry::new(Some(vec![3, 2, 1, 0]), 2),
            ]
        );
    }

    #[test]
    fn test_io_compaction_reg_switches() {
        let sparse = HashMap::<usize, _>::from([
            (111, CalendarEntry::new(Some(0), 1)),
            (112, CalendarEntry::new(Some(0), 1)),
            (115, CalendarEntry::new(Some(0), 1)),
            (131, CalendarEntry::new(Some(0), 1)),
            (132, CalendarEntry::new(Some(0), 1)),
            (133, CalendarEntry::new(Some(0), 1)),
        ]);

        assert_eq!(
            Calendar::compact(&sparse, 80),
            vec![
                CalendarEntry::new(None, 31),
                CalendarEntry::new(Some(0), 1),
                CalendarEntry::new(Some(0), 1),
                CalendarEntry::new(None, 2),
                CalendarEntry::new(Some(0), 1),
                CalendarEntry::new(None, 15),
                CalendarEntry::new(Some(0), 1),
                CalendarEntry::new(Some(0), 1),
                CalendarEntry::new(Some(0), 1),
            ]
        );
    }

    #[test]
    fn test_io_compaction() {
        let sparse = HashMap::<usize, _>::from([
            (111, CalendarEntry::new(Some(0), 1)),
            (112, CalendarEntry::new(Some(1), 2)),
            (114, CalendarEntry::new(None, 1)),
            (115, CalendarEntry::new(Some(10), 1)),
            (116, CalendarEntry::new(Some(20), 10)),
            (126, CalendarEntry::new(Some(30), 5)),
            (131, CalendarEntry::new(Some(0), 1)),
            (132, CalendarEntry::new(Some(0), 1)),
            (133, CalendarEntry::new(Some(0), 1)),
        ]);

        assert_eq!(
            Calendar::compact(&sparse, 80),
            vec![
                CalendarEntry::new(None, 31),
                CalendarEntry::new(Some(0), 3),
                CalendarEntry::new(None, 1),
                CalendarEntry::new(Some(10), 1),
                CalendarEntry::new(Some(20), 15),
                CalendarEntry::new(Some(0), 1),
                CalendarEntry::new(Some(0), 1),
                CalendarEntry::new(Some(0), 1),
            ]
        );
    }
}

// Performance experiments

// with calendar as vector
// running 4 tests
//     test gather                 ... bench:  22,383,468 ns/iter (+/- 547,052) = 178 MB/s
//     test gather_with_cal_entry  ... bench:  22,981,420 ns/iter (+/- 314,253) = 174 MB/s
//     test scatter                ... bench:  22,764,838 ns/iter (+/- 173,640) = 175 MB/s
//     test scatter_with_cal_entry ... bench:  22,500,503 ns/iter (+/- 200,850) = 177 MB/s
// running 3 tests
//     test gather                 ... bench:  22,879,155 ns/iter (+/- 245,477) = 174 MB/s
//     test scatter                ... bench:  23,238,504 ns/iter (+/- 130,252) = 172 MB/s
//     test scatter_with_cal_entry ... bench:  22,216,460 ns/iter (+/- 624,969) = 180 MB/s

// with calendar as array
// running 4 tests
//     test gather                 ... bench:  22,354,486 ns/iter (+/- 770,918) = 178 MB/s
//     test gather_with_cal_entry  ... bench:  22,795,415 ns/iter (+/- 436,740) = 175 MB/s
//     test scatter                ... bench:  22,778,451 ns/iter (+/- 273,762) = 175 MB/s
//     test scatter_with_cal_entry ... bench:  22,859,907 ns/iter (+/- 236,636) = 174 MB/s
// running 3 tests
//     test gather                 ... bench:  23,281,680 ns/iter (+/- 420,758) = 171 MB/s
//     test scatter                ... bench:  23,366,367 ns/iter (+/- 172,074) = 171 MB/s
//     test scatter_with_cal_entry ... bench:  22,178,757 ns/iter (+/- 250,834) = 180 MB/s
