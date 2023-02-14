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
use std::cell::RefCell;
use std::rc::Rc;

use crate::app::ServiceHandle;
use crate::calendar::CalendarVariant;
use crate::calendar::CalendarVariantRef;
use crate::calendar::{Buffering, BUFFERING_DOUBLE, BUFFERING_SINGLE};
use crate::mailbox::MailBox;
use crate::sim::OptionSimCallbacks;
use crate::specs::LinkStatus;
use crate::specs::ProvisionedComputeNode;
use crate::specs::ProvisionedLink;
use crate::specs::ProvisionedNode;
use crate::specs::ProvisionedSwitchNode;
use crate::specs::{Frequency, SystemSpec};
use crate::vcd::{VcdComponent, VcdWriter};
use crate::{LinkSpec, NodeSpec, Port};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunConfig {
    RunCalendar0,
    RunCalendar1,
}

impl From<RunConfig> for usize {
    fn from(run_config: RunConfig) -> usize {
        run_config.clone() as usize
    }
}

/// Computes the current metacycle given local cycles. In the double-buffering scenario the
/// metacycles may not be the same size,
///
///```text
/// E.g. cpm == [3, 7] and local_cycles == 15, M(i) denotes the i(th) metacycle,
///
///    M(0)   M(1)   M(2)   M(3)   M(4)
///   <---><-------><---><-------><---> ...
///    012  3456789  111  1111111  222
///                  012  3456789  012
///                         ^
///                         (local_cycles = 15) => M(3)
///```
pub fn metacycle<const BUFFERING: Buffering>(
    local_cycles: Cycle,
    cpm: [Cycle; BUFFERING],
) -> Cycle {
    let mut total_cpm = 0;
    for i in 0..cpm.len() {
        total_cpm += cpm[i];
    }
    let multiples = local_cycles / total_cpm;
    let offset = if (local_cycles % total_cpm) < cpm[0] {
        0
    } else {
        1
    };
    match BUFFERING {
        BUFFERING_SINGLE | BUFFERING_DOUBLE => BUFFERING * multiples + offset,
        _ => panic!("Unsupported buffering configuration."),
    }
}

// This enum exists to differentiate between when the IO unit (Gather/Scatter)
// is used on compute nodes vs. switches.
//
// This is an effect of double-buffering. While compute nodes will have double
// buffered IO memories, switches won't. However, switches still require two
// sets of calendars. When `IOConfig::SwitchIO` is active, only
// `ScatterEngine::memory[0]` is used.
#[derive(Clone, Debug)]
pub enum IOConfig {
    SwitchIO,
    ComputeIO,
}

impl Default for RunConfig {
    fn default() -> Self {
        Self::RunCalendar0
    }
}

impl RunConfig {
    fn toggle(&self) -> RunConfig {
        match self {
            RunConfig::RunCalendar0 => RunConfig::RunCalendar1,
            RunConfig::RunCalendar1 => RunConfig::RunCalendar0,
        }
    }
}

pub(super) mod compute;
pub(super) mod config;
pub(super) mod gather;
pub(super) mod scatter;
mod switch;

pub use switch::SwitchType;
pub(super) mod topologies;

/// Specialized specification for bittide hardware
pub type HardwareSpecType<const BUFFERING: Buffering> =
    SystemSpec<BUFFERING, Node<BUFFERING>, Link>;
pub type HardwareSpec = SystemSpec<{ BUFFERING_DOUBLE }, Node<{ BUFFERING_DOUBLE }>, Link>;

pub use crate::hw::compute::ComputeNode;
pub use crate::hw::switch::SwitchNode;

#[derive(Clone, Debug)]
pub enum Node<const BUFFERING: Buffering> {
    ComputeNode(ComputeNode<BUFFERING>),
    SwitchNode(SwitchNode<BUFFERING>),
}

impl<const BUFFERING: Buffering> Node<BUFFERING> {
    fn inner_node_spec(&self) -> &dyn NodeSpec<BUFFERING> {
        match self {
            Self::ComputeNode(compute) => compute as &dyn NodeSpec<BUFFERING>,
            Self::SwitchNode(switch) => switch as &dyn NodeSpec<BUFFERING>,
        }
    }

    fn mut_inner_node_spec(&mut self) -> &mut dyn NodeSpec<BUFFERING> {
        match self {
            Self::ComputeNode(compute) => compute as &mut dyn NodeSpec<BUFFERING>,
            Self::SwitchNode(switch) => switch as &mut dyn NodeSpec<BUFFERING>,
        }
    }

    fn mut_inner_provisioned_node(&mut self) -> &mut dyn ProvisionedNode<BUFFERING> {
        match self {
            Self::ComputeNode(compute) => compute as &mut dyn ProvisionedNode<BUFFERING>,
            Self::SwitchNode(switch) => switch as &mut dyn ProvisionedNode<BUFFERING>,
        }
    }

    fn inner_provisioned_node(&self) -> &dyn ProvisionedNode<BUFFERING> {
        match self {
            Self::ComputeNode(compute) => compute as &dyn ProvisionedNode<BUFFERING>,
            Self::SwitchNode(switch) => switch as &dyn ProvisionedNode<BUFFERING>,
        }
    }

    fn inner_vcd_component(&self) -> &dyn VcdComponent {
        match self {
            Self::ComputeNode(compute) => compute as &dyn VcdComponent,
            Self::SwitchNode(switch) => switch as &dyn VcdComponent,
        }
    }
}

impl<const BUFFERING: Buffering> NodeSpec<BUFFERING> for Node<BUFFERING> {
    fn name(&self) -> &str {
        self.inner_node_spec().name()
    }

    fn step(
        &mut self,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        self.mut_inner_node_spec().step(inputs, outputs, callbacks)
    }

    fn set_port_framing(&mut self, _port: Port, _lead: FramingLead) {
        unimplemented!();
    }

    fn into_mut_provisioned_node(&mut self) -> Option<&mut dyn ProvisionedNode<BUFFERING>> {
        Some(self.mut_inner_provisioned_node())
    }

    fn into_provisioned_node(&self) -> Option<&dyn ProvisionedNode<BUFFERING>> {
        Some(self.inner_provisioned_node())
    }
    fn into_provisioned_compute_node(&self) -> Option<&dyn ProvisionedComputeNode<BUFFERING>> {
        match self {
            Self::ComputeNode(compute) => Some(compute as &dyn ProvisionedComputeNode<BUFFERING>),
            Self::SwitchNode(_) => None,
        }
    }
    fn into_mut_provisioned_compute_node(
        &mut self,
    ) -> Option<&mut dyn ProvisionedComputeNode<BUFFERING>> {
        match self {
            Self::ComputeNode(compute) => {
                Some(compute as &mut dyn ProvisionedComputeNode<BUFFERING>)
            }
            Self::SwitchNode(_) => None,
        }
    }
    fn into_provisioned_switch_node(&self) -> Option<&dyn ProvisionedSwitchNode<BUFFERING>> {
        match self {
            Self::ComputeNode(_) => None,
            Self::SwitchNode(switch) => Some(switch as &dyn ProvisionedSwitchNode<BUFFERING>),
        }
    }
    fn into_mut_provisioned_switch_node(
        &mut self,
    ) -> Option<&mut dyn ProvisionedSwitchNode<BUFFERING>> {
        match self {
            Self::ComputeNode(_) => None,
            Self::SwitchNode(switch) => Some(switch as &mut dyn ProvisionedSwitchNode<BUFFERING>),
        }
    }
}

impl<const BUFFERING: Buffering> ProvisionedNode<BUFFERING> for Node<BUFFERING> {
    fn cycles_per_metacycle(&self) -> [Cycle; BUFFERING] {
        self.inner_provisioned_node().cycles_per_metacycle()
    }

    fn set_cycles_per_metacycle(&mut self, cpm: [Cycle; BUFFERING]) {
        self.mut_inner_provisioned_node()
            .set_cycles_per_metacycle(cpm)
    }

    fn set_scatter_memory_size(&mut self, port: Port, memory_size: usize) {
        self.mut_inner_provisioned_node()
            .set_scatter_memory_size(port, memory_size);
    }

    fn set_scatter_link_status(&mut self, port: Port, link_status: LinkStatus) {
        self.mut_inner_provisioned_node()
            .set_scatter_link_status(port, link_status);
    }

    fn set_gather_link_status(&mut self, port: Port, link_status: LinkStatus) {
        self.mut_inner_provisioned_node()
            .set_gather_link_status(port, link_status);
    }

    fn set_io_calendar(&mut self, calendar: IOCalendarVariant<BUFFERING>, port: Port) {
        self.mut_inner_provisioned_node()
            .set_io_calendar(calendar, port);
    }

    fn set_gather_memory_size(&mut self, port: Port, memory_size: usize) {
        self.mut_inner_provisioned_node()
            .set_gather_memory_size(port, memory_size);
    }

    fn get_scatter_memory_size(&self, port: Port) -> usize {
        self.inner_provisioned_node().get_scatter_memory_size(port)
    }

    fn get_gather_memory_size(&self, port: Port) -> usize {
        self.inner_provisioned_node().get_gather_memory_size(port)
    }

    fn metacycle(&self) -> Cycle {
        self.inner_provisioned_node().metacycle()
    }

    fn register_app(&mut self, service_handle: ServiceHandle, service: Rc<RefCell<Service>>) {
        self.mut_inner_provisioned_node()
            .register_app(service_handle, service)
    }
    fn set_calendar(&mut self, calendar: CalendarVariant<BUFFERING>) {
        self.mut_inner_provisioned_node().set_calendar(calendar)
    }

    fn step_gather(
        &mut self,
        port: Port,
        outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        self.mut_inner_provisioned_node()
            .step_gather(port, outputs, callbacks)
    }

    fn step_scatter(
        &mut self,
        port: Port,
        inputs: &[InputFrameRef],
        callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        self.mut_inner_provisioned_node()
            .step_scatter(port, inputs, callbacks)
    }

    fn advance_metacycle(&mut self) {
        self.mut_inner_provisioned_node().advance_metacycle();
    }

    fn set_starting_cycles(&mut self, cycle: Cycle) {
        self.mut_inner_provisioned_node().set_starting_cycles(cycle);
    }

    fn starting_cycles(&self) -> Cycle {
        self.inner_provisioned_node().starting_cycles()
    }

    fn local_cycles(&self) -> Cycle {
        self.inner_provisioned_node().local_cycles()
    }

    fn frequency(&self) -> Frequency {
        self.inner_provisioned_node().frequency()
    }

    fn set_frequency(&mut self, freq: Frequency) {
        self.mut_inner_provisioned_node().set_frequency(freq)
    }

    fn set_mailbox(&mut self, mailbox: MailBox) {
        self.mut_inner_provisioned_node().set_mailbox(mailbox);
    }

    fn get_mailbox(&self) -> Option<&MailBox> {
        self.inner_provisioned_node().get_mailbox()
    }

    fn set_crashed(&mut self, crashed: bool) {
        // In future we may want a NodeStatus struct or similar, which contains
        // additional info about the failure (e.g., which component has failed,
        // which bit has flipped, etc.).
        self.mut_inner_provisioned_node().set_crashed(crashed);
    }

    fn get_crashed(&self) -> bool {
        self.inner_provisioned_node().get_crashed()
    }
}

impl<const BUFFERING: Buffering> VcdComponent for Node<BUFFERING> {
    fn vcd_write_scope(&self, vcd_writer: Rc<RefCell<VcdWriter>>) {
        self.inner_vcd_component().vcd_write_scope(vcd_writer)
    }

    fn vcd_init(&self, vcd_writer: Rc<RefCell<VcdWriter>>) {
        self.inner_vcd_component().vcd_init(vcd_writer)
    }
}

impl<const BUFFERING: Buffering> From<ComputeNode<BUFFERING>> for Node<BUFFERING> {
    fn from(compute_node: ComputeNode<BUFFERING>) -> Node<BUFFERING> {
        Node::ComputeNode(compute_node)
    }
}

impl<const BUFFERING: Buffering> From<SwitchNode<BUFFERING>> for Node<BUFFERING> {
    fn from(switch_node: SwitchNode<BUFFERING>) -> Node<BUFFERING> {
        Node::SwitchNode(switch_node)
    }
}

#[derive(Clone, Debug)]
pub struct Link {
    src_port: Port,
    dst_port: Port,
    latency: Latency,
    frame_size: usize,
    frequency: Frequency,
}

impl NonFramingLinkTrait for Link {}

impl Link {
    fn src_port(src_port_idx: usize, frame_size: usize) -> Port {
        Port::new(
            src_port_idx,
            &PortProperties {
                direction: Direction::Outgoing,
                frame_size: frame_size.into(),
                ..Default::default()
            },
        )
    }

    fn dst_port(dst_port_idx: usize, frame_size: usize) -> Port {
        Port::new(
            dst_port_idx,
            &PortProperties {
                direction: Direction::Incoming,
                frame_size: frame_size.into(),
                ..Default::default()
            },
        )
    }

    pub fn from_config(
        src_port_idx: usize,
        dst_port_idx: usize,
        config: LinkConfiguration,
    ) -> Self {
        Self {
            src_port: Self::src_port(src_port_idx, config.frame_size),
            dst_port: Self::dst_port(dst_port_idx, config.frame_size),
            latency: Latency(config.latency),
            frame_size: config.frame_size,
            frequency: Frequency::new(config.frequency),
        }
    }
    // TODO(cascaval): do we need a constructor with Ports?
    // Opinion: hardware ports seem better off with just numbers, since it
    // is very likely that all the links to a node are homogeneous and fungible.
}

impl LinkSpec for Link {
    fn src_port(&self) -> Port {
        self.src_port
    }
    fn dst_port(&self) -> Port {
        self.dst_port
    }
    fn latency(&self) -> Latency {
        self.latency
    }
    fn set_latency(&mut self, latency: Latency) {
        self.latency = latency;
    }
    /// return the pair of (src_port, dst_port)
    fn get_ports(&self) -> (Port, Port) {
        (self.src_port, self.dst_port)
    }
    fn frame_size(&self) -> usize {
        self.frame_size
    }

    fn into_provisioned_link(&self) -> Option<&dyn ProvisionedLink> {
        Some(self)
    }

    fn into_mut_provisioned_link(&mut self) -> Option<&mut dyn ProvisionedLink> {
        Some(self)
    }
}

impl ProvisionedLink for Link {
    fn frequency(&self) -> Frequency {
        self.frequency
    }
    fn set_frequency(&mut self, freq: Frequency) {
        self.frequency = freq;
    }
}
