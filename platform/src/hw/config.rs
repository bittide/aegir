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

use crate::hw::Direction;
use crate::hw::Port;
use crate::Cycle;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

/// The size of the RX/TX memories.
///
/// Currently fixed, and the same for all links.
const RX_MEM_CAPACITY: usize = 255;
// TODO(cascaval): make these part of the node/link configuration.
// const TX_MEM_CAPACITY: usize = 255;

/// A default frame size
pub const FRAME_SIZE: usize = 64;

/// The maximum size for a Calendar.
///
/// Currently fixed, and the same for all scatter/gather/crossbar engines.
const CALENDAR_CAPACITY: usize = 1024;

// parameters for a switch
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SwitchConfiguration {
    pub frequency: usize,
    pub cycles_per_metacycle: Cycle,
    pub crossbar_latency: Cycle,
    pub input_link_count: usize,
    pub output_link_count: usize,
    pub starting_cycles: Cycle,
    pub link_configuration: LinkConfiguration,
}

impl Default for SwitchConfiguration {
    fn default() -> Self {
        Self {
            frequency: 1,
            cycles_per_metacycle: 1,
            crossbar_latency: 0,
            link_configuration: LinkConfiguration {
                calendar_size: 1,
                memory_size: 1,
                ..Default::default()
            },
            input_link_count: 0,
            output_link_count: 0,
            starting_cycles: rand::thread_rng().gen_range(0..100),
        }
    }
}

/// provides a set of parameters to configure a node
///
/// constructed programmatically or read from a config file.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct NodeConfiguration {
    pub frequency: usize,
    pub cycles_per_metacycle: Cycle,
    pub input_links: Vec<LinkConfiguration>,
    pub output_links: Vec<LinkConfiguration>,
    pub memory_size: usize, // in bytes
    pub num_threads: usize,
    pub starting_cycles: Cycle,
    // .. other harwdare capabilities
}

impl NodeConfiguration {
    pub fn num_inputs(&self) -> usize {
        self.input_links.len()
    }
    pub fn num_outputs(&self) -> usize {
        self.output_links.len()
    }
    pub fn add_link(&mut self, config: &LinkConfiguration, port: Port) {
        let port_index: usize = port.into();
        match port.direction() {
            Direction::Incoming => {
                if self.num_inputs() <= port_index {
                    self.input_links.resize(port_index + 1, Default::default());
                }
                self.input_links[port_index] = config.clone();
            }
            Direction::Outgoing => {
                if self.num_outputs() <= port_index {
                    self.output_links.resize(port_index + 1, Default::default());
                }
                self.output_links[port_index] = config.clone();
            }
        }
    }
}

impl Default for NodeConfiguration {
    fn default() -> Self {
        let mut rng = rand::thread_rng();
        let starting_cycles = rng.gen_range(0..100);
        Self {
            frequency: 1,
            cycles_per_metacycle: 1,
            input_links: Vec::new(),
            output_links: Vec::new(),
            memory_size: std::usize::MAX, // infinite memory!
            num_threads: 1,
            starting_cycles,
        }
    }
}

#[derive(Copy, Clone, Debug, Deserialize, Serialize)]
pub struct LinkConfiguration {
    pub frame_size: usize,
    pub calendar_size: usize,
    pub memory_size: usize,
    pub frequency: usize,
    pub latency: usize,
}

impl LinkConfiguration {
    pub fn new(
        frame_size: usize,
        calendar_size: usize,
        memory_size: usize,
        frequency: usize,
        latency: usize,
    ) -> Self {
        Self {
            frame_size: frame_size,
            calendar_size: calendar_size,
            memory_size: memory_size,
            frequency: frequency,
            latency: latency,
        }
    }
}

impl Default for LinkConfiguration {
    fn default() -> Self {
        Self {
            frame_size: FRAME_SIZE,
            calendar_size: CALENDAR_CAPACITY,
            memory_size: RX_MEM_CAPACITY,
            frequency: 1,
            latency: 0,
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Config {
    nodes: Vec<NodeConfiguration>,
    switches: Vec<SwitchConfiguration>,
}

impl Config {
    #[allow(dead_code)]
    pub fn from_file(file_name: &str) -> Self {
        let file = File::open(Path::new(file_name))
            .unwrap_or_else(|e| panic!("File {} not found. {:?}", file_name, e));
        let reader = BufReader::new(file);
        serde_yaml::from_reader(reader).unwrap()
    }
    #[allow(dead_code)]
    pub fn from_str(config: &str) -> Self {
        serde_yaml::from_str(config).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_yaml;

    #[test]
    fn read_yaml_config() {
        let conf_str = "---
nodes:
  - frequency: 1
    cycles_per_metacycle: 1
    input_links:
      - frame_size: 64
        calendar_size: 10
        memory_size: 20
        frequency: 1
        latency: 3
      - frame_size: 64
        calendar_size: 1024
        memory_size: 255
        frequency: 1
        latency: 0
    output_links:
      - frame_size: 64
        calendar_size: 1024
        memory_size: 255
        frequency: 1
        latency: 0
    memory_size: 100
    num_threads: 4
    starting_cycles: 5
  - frequency: 1
    cycles_per_metacycle: 1
    input_links:
      - frame_size: 64
        calendar_size: 1024
        memory_size: 255
        frequency: 1
        latency: 0
    output_links:
      - frame_size: 64
        calendar_size: 1024
        memory_size: 255
        frequency: 1
        latency: 0
      - frame_size: 64
        calendar_size: 1024
        memory_size: 255
        frequency: 1
        latency: 0
    memory_size: 2048
    num_threads: 1
    starting_cycles: 0
switches:
    - frequency: 1
      cycles_per_metacycle: 1
      crossbar_latency: 3
      link_configuration:
        calendar_size: 1
        memory_size: 1
        frame_size: 64
        frequency: 1
        latency: 0
      input_link_count: 3
      output_link_count: 4
      starting_cycles: 101
";
        let config = Config::from_str(&conf_str);
        assert_eq!(config.nodes.len(), 2);
        assert_eq!(config.nodes[0].memory_size, 100);
        assert_eq!(config.nodes[0].input_links.len(), 2);
        assert_eq!(config.nodes[0].input_links[0].calendar_size, 10);
        assert_eq!(config.nodes[0].input_links[0].frequency, 1);
        assert_eq!(config.nodes[0].input_links[0].latency, 3);
        assert_eq!(config.nodes[0].output_links.len(), 1);
        assert_eq!(config.nodes[0].starting_cycles, 5);
        assert_eq!(config.nodes[1].memory_size, 2048);
        assert_eq!(config.nodes[1].input_links.len(), 1);
        assert_eq!(config.nodes[1].input_links[0].calendar_size, 1024);
        assert_eq!(config.nodes[1].output_links.len(), 2);
        assert_eq!(config.nodes[1].starting_cycles, 0);
        assert_eq!(config.switches[0].frequency, 1);
        assert_eq!(config.switches[0].cycles_per_metacycle, 1);
        assert_eq!(config.switches[0].crossbar_latency, 3);
        assert_eq!(config.switches[0].input_link_count, 3);
        assert_eq!(config.switches[0].output_link_count, 4);
        assert_eq!(config.switches[0].link_configuration.calendar_size, 1);
        assert_eq!(config.switches[0].link_configuration.memory_size, 1);
        assert_eq!(config.switches[0].link_configuration.frame_size, 64);
        assert_eq!(config.switches[0].starting_cycles, 101);
        println!("{:#?}", config);
    }

    #[test]
    fn write_yaml_config() {
        let mut n1 = NodeConfiguration::default();
        n1.input_links.push(LinkConfiguration::default());
        n1.input_links.push(LinkConfiguration::default());
        n1.output_links.push(LinkConfiguration::default());
        let mut n2 = NodeConfiguration::default();
        n2.input_links.push(LinkConfiguration::default());
        n2.output_links.push(LinkConfiguration::default());
        n2.output_links.push(LinkConfiguration::default());

        let mut switch = SwitchConfiguration::default();
        switch.input_link_count = 3;
        switch.output_link_count = 4;

        let config = Config {
            nodes: vec![n1, n2],
            switches: vec![switch],
        };
        println!("{}", serde_yaml::to_string(&config).unwrap());
    }
}
