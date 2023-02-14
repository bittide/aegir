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

use std::mem;
use std::sync::{Mutex, RwLock};

use bits_derive::*;

use crate::*;

/// Messages we can log. These should be cheap to create to keep logging overhead low.
#[derive(Clone, Debug)]
pub enum PacketNetLog {
    MessageSent {
        from: PacketNetAddress,
        from_cycle: Cycle,
        to: PacketNetAddress,
    },
    MessageForwarded {
        from: PacketNetAddress,
        from_cycle: Cycle,
        to: PacketNetAddress,
        at: PacketNetAddress,
        at_cycle: Cycle,
        direction: u8,
    },
    MessageDropped {
        from: PacketNetAddress,
        from_cycle: Cycle,
        to: PacketNetAddress,
        at: PacketNetAddress,
        at_cycle: Cycle,
    },
    MessageReceived {
        from: PacketNetAddress,
        from_cycle: Cycle,
        to: PacketNetAddress,
        to_cycle: Cycle,
    },
}

type PacketNetLogData = Mutex<Vec<PacketNetLog>>;

/// A Bits-serializable handle to a shared log object.
#[derive(Copy, Clone, Bits)]
pub struct PacketNetLogHandle(u64);

static LOG_DATA: RwLock<Vec<PacketNetLogData>> = RwLock::new(Vec::new());

impl PacketNetLogHandle {
    pub fn new() -> PacketNetLogHandle {
        let mut log_vec = LOG_DATA.write().unwrap();
        let ret = log_vec.len();
        log_vec.push(Mutex::new(Vec::new()));
        PacketNetLogHandle(ret as u64)
    }

    /// Add an entry to the log.
    pub fn log(self, entry: PacketNetLog) {
        let log_vec = LOG_DATA.read().unwrap();
        log_vec[self.0 as usize].lock().unwrap().push(entry);
    }

    /// Return all log messages and clear the log.
    pub fn take_log(self) -> Vec<PacketNetLog> {
        let log_vec = LOG_DATA.read().unwrap();
        let mut entries = log_vec[self.0 as usize].lock().unwrap();
        mem::replace(&mut *entries, Vec::new())
    }
}
