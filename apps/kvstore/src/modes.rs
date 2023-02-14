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

use std::str::FromStr;
use structopt::StructOpt;

// Run corresponds to running the application topology
// Sim corresponds to running the application on a 1:1 hardware topology.
#[derive(StructOpt, Debug)]
pub enum RunMode {
    Run,
    Sim,
}

impl FromStr for RunMode {
    type Err = std::io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Run" => Ok(RunMode::Run),
            "Sim" => Ok(RunMode::Sim),
            _ => Err(Self::Err::new(
                std::io::ErrorKind::Other,
                format!("Invalid run mode: {}", s),
            )),
        }
    }
}

// Specify the type of the server topology
#[derive(StructOpt, Debug)]
pub enum ServerConfig {
    Single,
    Sharded,
    Replicated,
}

impl FromStr for ServerConfig {
    type Err = std::io::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "Single" => Ok(ServerConfig::Single),
            "Sharded" => Ok(ServerConfig::Sharded),
            "Replicated" => Ok(ServerConfig::Replicated),
            _ => Err(Self::Err::new(
                std::io::ErrorKind::Other,
                format!("Invalid server configuration: {}", s),
            )),
        }
    }
}
