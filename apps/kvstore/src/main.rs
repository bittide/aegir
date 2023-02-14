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
use structopt::StructOpt;

use kvstore::{RunMode, ServerConfig};

#[derive(StructOpt)]
#[structopt(name = "kv-store", about = "A distributed bittide key-value store")]
struct Arguments {
    /// supported modes: Run, Sim
    #[structopt(short, long, default_value = "Run")]
    mode: RunMode,
    /// supported configurations: Single, Sharded
    #[structopt(short, long, default_value = "Single")]
    server_config: ServerConfig,
    #[structopt(short, long, default_value = "300")]
    cycles: usize,
}

fn main() {
    let args = Arguments::from_args();

    let _logger = env_logger::builder()
        .filter(Some("kvstore"), log::LevelFilter::Trace)
        .target(Target::Stderr)
        .init();

    match args.mode {
        RunMode::Run => {
            kvstore::run_app(args.cycles, args.server_config).expect("Failed to run application")
        }
        RunMode::Sim => kvstore::simulate_app(args.cycles, args.server_config)
            .expect("Failed to simulate application"),
    }
}
