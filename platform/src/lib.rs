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

mod app;
mod bootstrap;
mod calendar;
mod error;
mod hw;
mod mailbox;
mod ports;
mod scheduler;
mod sim;
pub mod specs;
mod vcd;

// public node configurations (e.g., fan_in, fan_out)
pub mod predefined;

// Public types
// type to use for cycles
pub type Cycle = usize;

// TODO(cascaval): add a prelude for all these types.
pub use crate::app::{Application, Connection, Service};
pub use crate::calendar::IOCalendarVariant;
pub use crate::calendar::{Buffering, BUFFERING_DOUBLE, BUFFERING_SINGLE};
pub use crate::error::Error;
pub use crate::hw::config::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};
pub use crate::hw::topologies::fat_tree;
pub use crate::hw::IOConfig;
pub use crate::hw::{HardwareSpec, HardwareSpecType, Link, Node};
pub use crate::ports::{FrameSize, Port, PortLabel, PortProperties, RttiType};
pub use crate::scheduler::AllocationPolicy;
pub use crate::scheduler::MappingConfiguration1x1;
pub use crate::scheduler::MappingConfiguration1x1Network;
pub use crate::scheduler::RandomAllocation;
pub use crate::sim::generate_system_spec;
pub use crate::sim::FailureProperties;
pub use crate::sim::HardwareSystemSimulation;
pub use crate::sim::Inspect;
pub use crate::sim::SoftwareSystemSimulation;
pub use crate::sim::SystemSimulationCallbacks;
pub use crate::sim::SystemSimulationTrait;
pub use crate::specs::Action;
pub use crate::specs::{
    Data, DataWithValidity, InputFrameRef, LoopbackRef, OutputFrameRef, SystemContext,
};
pub use crate::specs::{FramingLead, Frequency, FrequencyFactor, Latency};
pub use crate::specs::{FramingLinkTrait, LinkSpec, NodeSpec, NonFramingLinkTrait};
pub use crate::vcd::VcdWriter;
pub use petgraph::graph::{EdgeIndex, NodeIndex};
pub use petgraph::Direction;

pub use crate::sim::{simulate_bittide, simulate_bittide_app};
// for benchmarking
pub use crate::calendar::CalendarEntry;
pub use crate::hw::gather::GatherEngine;
pub use crate::hw::scatter::ScatterEngine;
