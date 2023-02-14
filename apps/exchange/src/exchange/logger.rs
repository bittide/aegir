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

use serde_json;
use std::fs::OpenOptions;
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::exchange::{ExchangeResult, FileName};

waves::action_fn! { logger (logname: FileName, len: u64) (result: ExchangeResult) -> () {
    // append the result to the the log identified by logname
    let logname = std::str::from_utf8(&logname[0..(len as usize)])
        .expect("Failed to decode logfile name");
    let log = OpenOptions::new()
        .append(true)
        .create(true)
        .open(Path::new(logname))
        .unwrap_or_else(|err| panic!("Failed to open log file {} for writing: {}", logname, err));
    let mut writer = BufWriter::new(log);
    writer.write(b"\n").expect("Failed to write newline");
    serde_json::to_writer_pretty(writer, &result).expect("Failed to write trades to log");
}}
