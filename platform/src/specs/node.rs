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

//! interface for nodes in a topology (system specification)

use super::*;
use crate::app::ServiceHandle;
use crate::calendar::Buffering;
use crate::calendar::{CalendarVariant, CalendarVariantRef, IOCalendarVariant};
use crate::hw::compute::HostMemoryCfg;
use crate::hw::SwitchType;
use crate::mailbox::MailBox;
use crate::ports::{PortLabel, PortProperties};
use crate::sim::OptionSimCallbacks;
use crate::{Cycle, Service};
use std::cell::RefCell;
use std::rc::Rc;

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum LinkStatus {
    Up,
    Down,
}

impl std::fmt::Display for LinkStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Self::Up => write!(f, "Up"),
            Self::Down => write!(f, "Down"),
        }
    }
}

pub trait NodeSpec<const BUFFERING: Buffering> {
    /// nodes have names
    fn name(&self) -> &str;

    /// executes the node for a single cycle with inputs, outputs.
    /// nodes maintain their own state, and will pass appropriately to actions.
    fn step(
        &mut self,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error>;

    // OPINION(tammo):  frequency could be more expressive -- for example we could allow
    // specification of something like "run this node action during the first 5ms out of the first
    // two sets of 100ms every second -- ie 2 times per second but at specific times"; supporting a
    // specification like this would make the math around aligning frequencies between linked nodes
    // incredibly complicated and most of the expressible configurations would be illegal;
    // additionally the underlying motivation for constraints of this kind is assumed to be implied
    // performance constraints (duration from system input A to output B must be less than X
    // milliseconds, etc); therefore we explicitly do not want additional expressiveness, and do
    // expect actual performance constraints will suffice to meet the underlying needs

    fn set_port_framing(&mut self, port: Port, lead: FramingLead);
    fn into_application_node(&self) -> Option<&dyn ApplicationNode> {
        None
    }
    fn into_mut_application_node(&mut self) -> Option<&mut dyn ApplicationNode> {
        None
    }
    fn into_provisioned_node(&self) -> Option<&dyn ProvisionedNode<BUFFERING>> {
        None
    }
    fn into_mut_provisioned_node(&mut self) -> Option<&mut dyn ProvisionedNode<BUFFERING>> {
        None
    }
    fn into_stateful_node(&self) -> Option<&dyn StatefulNode> {
        None
    }
    fn into_provisioned_switch_node(&self) -> Option<&dyn ProvisionedSwitchNode<BUFFERING>> {
        None
    }
    fn into_provisioned_compute_node(&self) -> Option<&dyn ProvisionedComputeNode<BUFFERING>> {
        None
    }
    fn into_mut_provisioned_switch_node(
        &mut self,
    ) -> Option<&mut dyn ProvisionedSwitchNode<BUFFERING>> {
        None
    }
    fn into_mut_provisioned_compute_node(
        &mut self,
    ) -> Option<&mut dyn ProvisionedComputeNode<BUFFERING>> {
        None
    }
}

pub trait ApplicationNode {
    // TODO(cascaval): consider better naming
    fn set_ports_properties(&mut self, props: &[(PortLabel, PortProperties)]);
    fn get_port(&self, label: &PortLabel) -> Option<&Port>;

    // TODO(sgrayson): Define a generic unit?
    // how often the node action should execute relative to the system root frequency
    fn rate_of_service(&self) -> FrequencyFactor;
    fn set_rate_of_service(&mut self, freq: FrequencyFactor);

    /// Runs the action function of the application.
    /// Call this instead of Node::step() when running the action function.
    /// This exists so that we don't need to stick a SystemContext into every
    /// step() definition, where it doesn't make sense. The SystemContext also
    /// is painful to statically set on the ApplicationNode directly, as it
    /// needs to embed a reference to the owning compute node so that it can
    /// access state from its host, but the caller holds a mutable borrow
    /// on the compute node when it calls in to run the service node; so the
    /// context can't borrow the compute node again without violating the
    /// runtime borrow checker rules. So we opted to pass the SystemContext
    /// in directly as a parameter.
    fn run_action_function(
        &mut self,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
        sys: &dyn SystemContext,
    ) -> Result<(), Error>;
}

pub trait ProvisionedNode<const BUFFERING: Buffering> {
    /// number of local cycles in a metacycle
    fn cycles_per_metacycle(&self) -> [Cycle; BUFFERING];
    /// set the number of cycles per metacycle
    fn set_cycles_per_metacycle(&mut self, cpm: [Cycle; BUFFERING]);
    /// the current metacycle
    fn metacycle(&self) -> Cycle;
    /// The start cycle of the node.
    fn starting_cycles(&self) -> Cycle;
    fn set_starting_cycles(&mut self, cycle: Cycle);
    /// The current local cycles of the node.
    fn local_cycles(&self) -> Cycle;
    fn register_app(&mut self, service_handle: ServiceHandle, service: Rc<RefCell<Service>>);
    fn set_calendar(&mut self, calendar: CalendarVariant<BUFFERING>);
    fn set_io_calendar(&mut self, calendar: IOCalendarVariant<BUFFERING>, port: Port);
    fn step_gather(
        &mut self,
        port: Port,
        outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error>;
    fn step_scatter(
        &mut self,
        port: Port,
        inputs: &[InputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error>;
    fn set_scatter_memory_size(&mut self, port: Port, memory_size: usize);
    fn set_gather_memory_size(&mut self, port: Port, memory_size: usize);
    fn set_gather_link_status(&mut self, port: Port, link_status: LinkStatus);
    fn set_scatter_link_status(&mut self, port: Port, link_status: LinkStatus);
    fn get_scatter_memory_size(&self, port: Port) -> usize;
    fn get_gather_memory_size(&self, port: Port) -> usize;
    fn advance_metacycle(&mut self);
    fn frequency(&self) -> Frequency;
    fn set_frequency(&mut self, freq: Frequency);
    fn set_mailbox(&mut self, mailbox: MailBox);
    fn get_mailbox(&self) -> Option<&MailBox>;
    fn set_crashed(&mut self, crashed: bool);
    fn get_crashed(&self) -> bool;
}

pub trait StatefulNode {
    fn persistent_state(&self) -> Option<&Data>;
    fn persistent_state_mut(&mut self) -> LoopbackRef;
    fn set_persistent_state(&mut self, state: Data);
}

pub trait ProvisionedComputeNode<const BUFFERING: Buffering> {
    fn get_node_calendar(&self) -> Option<CalendarVariantRef<BUFFERING>>;
    fn get_scatter_calendar(&self, port: Port) -> Option<CalendarVariantRef<BUFFERING>>;
    fn get_gather_calendar(&self, port: Port) -> Option<CalendarVariantRef<BUFFERING>>;
    fn get_host_memory_cfg(&self) -> &HostMemoryCfg<BUFFERING>;
}

pub trait ProvisionedSwitchNode<const BUFFERING: Buffering> {
    fn crossbar_latency(&self) -> Latency;
    fn get_crossbar_calendar(&self) -> Option<CalendarVariantRef<BUFFERING>>;
    fn get_scatter_calendar(&self, port: Port) -> Option<CalendarVariantRef<BUFFERING>>;
    fn get_gather_calendar(&self, port: Port) -> Option<CalendarVariantRef<BUFFERING>>;
    fn switch_type(&self) -> SwitchType;
}
