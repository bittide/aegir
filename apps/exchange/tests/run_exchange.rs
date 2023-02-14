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

use env_logger::Target;
use std::fs::File;
use std::path::Path;

#[test]
fn test_run_exchange() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile =
        File::create(logpath.join("run_exchange_app.log")).expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    exchange::exchange::run_exchange_app("test_run_exchange_app_10.log", CYCLES, None)
        .expect("Failed to run simulation");
}
