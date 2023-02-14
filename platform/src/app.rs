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

use std::collections::HashMap;

use super::*;

use crate::calendar::APPLICATION_NODE;
use crate::ports::{PortMap, PortProperties};
use crate::sim::OptionSimCallbacks;
use crate::specs::GraphId;
use crate::specs::{ApplicationNode, FramingLinkTrait, StatefulNode, SystemContext, SystemSpec};
use crate::vcd::ChangeValue;
use crate::{Action, LinkSpec, LoopbackRef, NodeSpec};
use crate::{Error, Port};

use std::cell::RefCell;
use std::fmt::Display;
use std::fmt::Formatter;

/// Specialized specification for an application
pub type Application = SystemSpec<{ APPLICATION_NODE }, Service, Connection>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ServiceHandle {
    pub app_id: GraphId,

    // Index of node in the application.
    pub service_id: NodeIndex,
}

impl ServiceHandle {
    pub fn new(app_id: GraphId, service_index: NodeIndex) -> Self {
        Self {
            app_id,
            service_id: service_index,
        }
    }
}

impl Display for ServiceHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "App:{}Service:{}", self.app_id, self.service_id.index())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CommsHandle {
    pub app_id: GraphId,
    pub edge_id: EdgeIndex,
}

impl CommsHandle {
    pub fn new(app_id: GraphId, edge_id: EdgeIndex) -> Self {
        Self { app_id, edge_id }
    }
}

impl<NS, LS> SystemSpec<APPLICATION_NODE, NS, LS>
where
    NS: NodeSpec<APPLICATION_NODE> + ApplicationNode + Sized + std::fmt::Debug,
    LS: LinkSpec + FramingLinkTrait + Sized + std::fmt::Debug,
{
    /// Given a fully constructed graph, normalize the frequencies of all
    /// nodes, so that we can correctly compute the serialization.
    ///
    /// Must be called before iterating over the graph with the visitor.
    pub(crate) fn normalize_frequencies(&self) {
        // assert!(
        //     self.visitor.is_empty(),
        //     "Node frequencies must be normalized before traversing the graph"
        // );
        if self.topo.node_count() == 0 {
            return;
        }
        // greatest common divisor node frequency in the system;  all nodes frequencies are defined
        // as integer-multiples of the root and execute an integral number of cycles for each root
        // cycle
        let init_index = self.topo.node_indices().min().unwrap();
        let init_freq = self
            .get_node(init_index)
            .borrow()
            .into_application_node()
            .unwrap()
            .rate_of_service()
            .0;
        let root_frequency = self.topo.node_weights().fold(init_freq, |gcd, node| {
            num::integer::gcd(
                gcd,
                node.borrow()
                    .into_application_node()
                    .unwrap()
                    .rate_of_service()
                    .0,
            )
        });

        // normalize the specified node frequencies using the root
        // note that we can't use the visitor, so we iterate through nodes directly
        for node in self.topo.node_weights() {
            let freq = node
                .borrow()
                .into_application_node()
                .unwrap()
                .rate_of_service()
                .0;
            node.borrow_mut()
                .into_mut_application_node()
                .unwrap()
                .set_rate_of_service(FrequencyFactor(freq / root_frequency));
        }
    }

    /// unidirectional link between nodes
    ///
    /// under simple conditions where frequencies across the link match, each side processes (read or
    /// write) one frame of data each cycle and the latency is likewise measured in cycles;  when the
    /// node frequencies across the link do not match, framing of data and latency measurement gets
    /// more complicated
    ///
    /// let freq_gcd be the greatest common divisor of both frequencies, and then let src_ratio and
    /// dst_ratio be the respective multipliers to derive the corresponding node frequencies from
    /// freq_gcd;  framing leadership indicates which side determines the link bandwidth, defined as
    /// the lead side always processesing one frame per local cycle (thus deciding the link
    /// bandwidth); the follower (non-lead) side will process lead_ratio frames over follower_ratio
    /// local cycles (the same lead_ratio frames persist in the corresponding IO memory for
    /// follower_ratio cycles; follower is src or dst, opposite of lead)
    ///
    /// the frequency of the link itself is thus freq_gcd, and latency is specified in that unit;
    /// bandwidth is lead_ratio frames per link-cycle and the number of frames in-flight on-the-wire
    /// (so to speak) is thus lead_ratio * latency
    ///
    /// some examples:
    ///
    /// (1) src_freq is 1 (and lead), dst_freq is 1, and latency is 1; link freq thus is 1, with 1
    /// frame per cycle everywhere (and 1 frame on-the-wire)
    ///
    /// (2) src_freq is 2 (and lead), dst_freq is 6, and latency is 2; link freq is thus 2; src
    /// writes 1 frame per local cycle, dst reads 1 frame per 3 local cycles, and 2 frames are on-
    /// the-wire
    ///
    /// (3) src_freq is 6 (and lead), dst_freq is 2, and latency is 2; link freq is thus 2; src
    /// writes 1 frame per local cycle, dst reads 3 frames per local cycle, and 6 frames are on-the-
    /// wire
    ///
    /// (4) src_freq is 6, dst_freq is 2 (and lead), and latency is 2; link freq is thus 2; src
    /// writes 1 frames per 3 local cycles, dst reads 1 frame per local cycle, and 2 frames are on-
    /// the-wire
    ///
    /// (5) src_freq is 2, dst_freq is 6 (and lead), and latency is 2; link freq is thus 2; src
    /// writes 3 frame per local cycle, dst reads 1 frame per local cycle, and 6 frames are on-the-
    /// wire
    ///
    /// (6) src_freq is 5 (and lead), dst_freq is 7, and latency is 3; link freq is thus 1; src
    /// writes 1 frame per local cycle, dst reads 5 frames every 7 local cycles, and 15 frames are
    /// on-the- wire
    ///
    /// (7) src_freq is 7, dst_freq is 5 (and lead), and latency is 3; link freq is thus 1; src
    /// writes 5 frames per 7 local cycles, dst reads 1 frame per local cycle, and 15 frames are on-
    /// the-wire
    ///
    /// (8) src_freq is 7 (and lead), dst_freq is 5, and latency is 3; link freq is thus 1; src
    /// writes 1 frame per local cycle, dst reads 7 frames every 5 local cycles, and 21 frames are
    /// on-the- wire
    ///
    /// (9) src_frq is 5, dst_freq is 7 (and lead), and latency is 3; link freq is thus 1; src writes
    /// 7 frames per 5 local cycles, dst reads 1 frame per local cycle, and 21 frames are on-the-wire
    ///
    /// Note that multiple edges are allowed between two nodes. However, we
    /// ensure that they do not connect the same ports.
    pub fn link_simplex_framing(
        &mut self,
        src: NodeIndex,
        dst: NodeIndex,
        link: LS,
        framing_lead: FramingLead,
    ) -> EdgeIndex {
        let src_node = self.get_node(src);
        let dst_node = self.get_node(dst);
        for e in self.topo.edges_connecting(src, dst) {
            assert!(
                e.weight().src_port() != link.src_port(),
                "Source port {} already connected!",
                link.src_port()
            );
            assert!(
                e.weight().dst_port() != link.dst_port(),
                "Dest port {} already connected!",
                link.src_port()
            );
        }

        let src_frequency = src_node.borrow().rate_of_service().0;
        let dst_frequency = dst_node.borrow().rate_of_service().0;
        let freq_gcd = FrequencyFactor(num::integer::gcd(src_frequency, dst_frequency)).0;
        let src_gcd_ratio = FrequencyFactor(src_frequency / freq_gcd);
        let dst_gcd_ratio = FrequencyFactor(dst_frequency / freq_gcd);
        let (lead_ratio, follower_ratio) = match framing_lead {
            FramingLead::Src => (src_gcd_ratio, dst_gcd_ratio),
            FramingLead::Dst => (dst_gcd_ratio, src_gcd_ratio),
        };

        // if the ports do not have the same framing lead, we should update
        // them for consistency. Why here? because in our current
        // implementation, ports (and connection) are created when there is
        // no knowledge of who will be the lead.
        if link.src_port().framing_lead() != framing_lead {
            self.get_node(src)
                .borrow_mut()
                .set_port_framing(link.src_port(), framing_lead);
            self.get_node(dst)
                .borrow_mut()
                .set_port_framing(link.dst_port(), framing_lead);
        }

        let edge_idx = self.topo.add_edge(src, dst, link);
        // we just added the edge, so it should be safe to unwrap!
        self.topo.edge_weight_mut(edge_idx).unwrap().set_framing(
            framing_lead,
            lead_ratio,
            follower_ratio,
        );
        edge_idx
    }
}

/// Application node
///
/// An application node captures the user level action and the persistent state.
/// In addition, it has metadata to define its connectivity and rate of service.
#[derive(Clone)]
pub struct Service {
    name: String,
    action: Action,
    state: Option<Data>,
    frequency: FrequencyFactor,
    portmap: PortMap,
    // Cache get_msg_size lookups via memoization.
    msg_size_cache: RefCell<HashMap<Port, usize>>,
}

impl Service {
    pub fn new(
        name: &str,
        action: Action,
        state: Option<Data>,
        frequency: FrequencyFactor,
    ) -> Self {
        Self {
            name: String::from(name),
            action,
            state,
            frequency,
            portmap: PortMap::new(),
            msg_size_cache: RefCell::new(HashMap::new()),
        }
    }

    pub fn get_msg_size(&self, port: Port) -> usize {
        if let Some(msg_size) = self.msg_size_cache.borrow().get(&port) {
            return *msg_size;
        }
        for (_, v) in self.portmap.iter() {
            if *v == port {
                self.msg_size_cache
                    .borrow_mut()
                    .insert(port, v.frame_size());
                return v.frame_size();
            }
        }
        panic!(
            "Every port is required to have a message size, offending service: {:?} port: {:?}.",
            self.name(),
            port
        )
    }
}

impl NodeSpec<{ APPLICATION_NODE }> for Service {
    fn step(
        &mut self,
        _inputs: &[InputFrameRef],
        _outputs: &mut [OutputFrameRef],
        _callbacks: OptionSimCallbacks,
    ) -> Result<(), Error> {
        panic!("call run_action_function instead.");
    }

    fn name(&self) -> &str {
        self.name.as_str()
    }

    fn set_port_framing(&mut self, port: Port, lead: FramingLead) {
        self.portmap.iter_mut().for_each(|(_, v)| {
            if *v == port {
                v.set_framing_lead(lead);
            }
        })
    }
    fn into_application_node(&self) -> Option<&dyn ApplicationNode> {
        Some(self)
    }
    fn into_mut_application_node(&mut self) -> Option<&mut dyn ApplicationNode> {
        Some(self)
    }
    fn into_stateful_node(&self) -> Option<&dyn StatefulNode> {
        Some(self)
    }
}

impl ApplicationNode for Service {
    fn set_ports_properties(&mut self, props: &[(PortLabel, PortProperties)]) {
        self.portmap = crate::ports::to_portmap(props);
    }
    fn get_port(&self, label: &PortLabel) -> Option<&Port> {
        self.portmap.get(label)
    }

    fn rate_of_service(&self) -> FrequencyFactor {
        self.frequency
    }

    fn set_rate_of_service(&mut self, freq: FrequencyFactor) {
        self.frequency = freq;
    }

    fn run_action_function(
        &mut self,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        callbacks: OptionSimCallbacks,
        sys: &dyn SystemContext,
    ) -> Result<(), Error> {
        (self.action)(self.state.as_mut(), inputs, outputs, sys);
        if let Some(state) = self.persistent_state() {
            callbacks.vcd(|writer| {
                writer.borrow_mut().change_input_frame_ref(
                    "state",
                    Some(state),
                    state.len(),
                    ChangeValue::Defer,
                )
            });
        }
        Ok(())
    }
}

impl StatefulNode for Service {
    fn persistent_state(&self) -> Option<&Data> {
        if self.state.is_some() {
            self.state.as_ref()
        } else {
            None
        }
    }

    fn persistent_state_mut(&mut self) -> LoopbackRef {
        if self.state.is_some() {
            self.state.as_mut()
        } else {
            None
        }
    }
    fn set_persistent_state(&mut self, state: Data) {
        self.state = Some(state)
    }
}

impl std::fmt::Debug for Service {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // fn type_name_of<T>(_: T) -> &'static str {
        //     std::any::type_name::<T>()
        // }
        // // useless, does not contain the name, only the type, which we know!
        // let action_str = format!("{}", type_name_of(self.action));
        let action_str = format!("@ {:p}", self.action as *const usize);
        f.debug_struct("Service")
            .field("action", &action_str)
            .field("state", &self.state)
            .field("frequency", &self.frequency)
            .field("portmap", &self.portmap)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct Connection {
    src_port: Port,
    dst_port: Port,
    frame_size: usize,
    framing_lead: FramingLead,
    follower_batch_size: usize,
    follower_batch_cycles: usize,
}

impl Connection {
    /// this is the correct way to specify app connections.
    pub fn new(src_port: &Port, dst_port: &Port) -> Self {
        assert_eq!(
            src_port.frame_size(),
            dst_port.frame_size(),
            "Mismatched frame sizes for ports {} {} -> {} {}",
            src_port,
            src_port.frame_size(),
            dst_port,
            dst_port.frame_size()
        );
        assert_eq!(
            src_port.framing_lead(),
            dst_port.framing_lead(),
            "Mismatched framing leads for ports {} {:?} -> {} {:?}",
            src_port,
            src_port.framing_lead(),
            dst_port,
            dst_port.framing_lead()
        );
        Self {
            src_port: *src_port,
            dst_port: *dst_port,
            frame_size: src_port.frame_size(),
            framing_lead: src_port.framing_lead(),
            follower_batch_size: 0,
            follower_batch_cycles: 0,
        }
    }

    /// constructor for testing.
    ///
    /// Connection::new() implies a lot of boiler plate in tests for this applications.
    /// that boiler plate is handled by waves::action!, but our tests do not use that,
    /// so we also have a constructor that specifies directly the frame sizes.
    #[cfg(test)]
    pub(crate) fn new_for_testing(src_port: usize, dst_port: usize, frame_size: usize) -> Self {
        Self {
            src_port: Port::new(
                src_port,
                &PortProperties {
                    direction: Direction::Outgoing,
                    frame_size: frame_size.into(),
                    ..Default::default()
                },
            ),
            dst_port: Port::new(
                dst_port,
                &PortProperties {
                    direction: Direction::Incoming,
                    frame_size: frame_size.into(),
                    ..Default::default()
                },
            ),
            frame_size: frame_size,
            framing_lead: FramingLead::Src,
            follower_batch_size: 0,
            follower_batch_cycles: 0,
        }
    }
}

impl FramingLinkTrait for Connection {
    fn framing_lead(&self) -> FramingLead {
        self.framing_lead
    }
    fn follower_batch_size(&self) -> usize {
        self.follower_batch_size
    }
    fn follower_batch_cycles(&self) -> usize {
        self.follower_batch_cycles
    }
    fn set_framing(
        &mut self,
        framing_lead: FramingLead,
        lead_framing: FrequencyFactor,
        follower_framing: FrequencyFactor,
    ) {
        self.framing_lead = framing_lead;
        self.follower_batch_size = lead_framing.0;
        self.follower_batch_cycles = follower_framing.0;
    }
}

impl LinkSpec for Connection {
    fn src_port(&self) -> Port {
        self.src_port
    }
    fn dst_port(&self) -> Port {
        self.dst_port
    }
    /// While idiomatic SDF notations have annotated edges in the graph to
    /// specify delays, the bittide application model reinforces the idea that
    /// one can not delay data en route between two nodes, and consequently
    /// requires the application writer to implement such sample latencies in
    /// their service function.
    fn latency(&self) -> Latency {
        // cascaval@ connections for an application have no latency. the data
        // produced this cycle is available the next cycle to the other node.
        // This is enforced by the system serialization.
        Latency(0)
    }
    fn set_latency(&mut self, _latency: Latency) {
        unimplemented!("Sample delays should be implemented by the service function.");
    }
    /// return the pair of (src_port, dst_port)
    fn get_ports(&self) -> (Port, Port) {
        (self.src_port, self.dst_port)
    }
    fn frame_size(&self) -> usize {
        self.frame_size
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ports::{FrameSize, RttiType};
    use bits::Bits;
    use bitvec::prelude::*;

    use crate::sim::SoftwareSystemSimulation;
    // use crate::LoopbackRef;

    #[track_caller]
    fn incr_action(
        state: LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        log::trace!(
            " state: {:?}\n inputs: {:?}\n outputs: {:?}",
            state,
            inputs,
            outputs
        );
        if let Some(mut state_bits) = state {
            let counter = u8::unpack(state_bits.as_bitslice()) + 1;
            log::trace!(" counter {}", counter);
            counter.pack_to(&mut state_bits);
        }
    }

    #[test]
    fn test_app() {
        let freq = FrequencyFactor(1);
        let mut app_spec = Application::new();
        let state = Some(bitvec![0; 8].into_boxed_bitslice());
        let mut n1 = Service::new("n1", incr_action, state.clone(), freq);
        let mut n2 = Service::new("n2", incr_action, state.clone(), freq);
        let src_port_spec = vec![(
            PortLabel::from("output"),
            PortProperties {
                direction: Direction::Outgoing,
                frame_size: FrameSize::Computed(RttiType::new::<u8>()),
                ..PortProperties::default()
            },
        )];
        n1.set_ports_properties(&src_port_spec);
        let dst_port_spec = vec![(
            PortLabel::from("input"),
            PortProperties {
                direction: Direction::Incoming,
                frame_size: FrameSize::Computed(RttiType::new::<u8>()),
                ..PortProperties::default()
            },
        )];
        n2.set_ports_properties(&dst_port_spec);
        let s1 = app_spec.add_node(n1);
        let s2 = app_spec.add_node(n2);
        let link_spec = Connection::new(
            app_spec
                .get_node(s1)
                .borrow()
                .get_port(&"output".into())
                .unwrap_or_else(|| panic!("Missing 'output' port!")),
            app_spec
                .get_node(s2)
                .borrow()
                .get_port(&"input".into())
                .unwrap_or_else(|| panic!("Missing 'input' port!")),
        );
        let _l1 = app_spec.link_simplex_framing(s1, s2, link_spec, FramingLead::Src);

        const CYCLES: usize = 10;
        let mut sim = SoftwareSystemSimulation::new(&mut app_spec);
        for cycle in 0..CYCLES {
            sim.simulate_system_one_cycle(&mut app_spec, &mut SystemSimulationCallbacks::default());
            let n1 = app_spec.get_node(s1);
            let n2 = app_spec.get_node(s2);
            assert_eq!(
                u8::unpack(n1.borrow().persistent_state().unwrap()),
                (cycle + 1) as u8
            );
            assert_eq!(
                u8::unpack(n2.borrow().persistent_state().unwrap()),
                (cycle + 1) as u8
            );
        }
    }
    // TODO(cascaval): add test for late binding of state (set_persistent_state)
}
