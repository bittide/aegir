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

//! The bittide bootstrapping protocol

//! The protocol is documented in [bootstrap](../../../../docs/bootstrap-v2.pdf)
//!
//! TODO:
//!   - implement support for switches; this implies:
//!     - adding management (compute) capabilities to SwitchNode (the management unit)
//!     - generating calendars for switches to enable communication with the mgmt unit
//!   - integrating bootstrap into the simulation initialization
//!   - accounting for the bootstrap quanta when scheuling, since bootstrap needs to
//!     run continuously to discover topology changes
//!   - add application loading as part of the protocol
//!
//! When the integration happens, remove #[allow(dead_code)]
#![allow(dead_code)]
#![allow(unused_imports)]

use crate::app::ServiceHandle;
use crate::calendar::BUFFERING_DOUBLE;
use crate::calendar::{Buffering, CalendarVariant, IOCalendarVariant};
use crate::calendar::{CalendarEntry, NodeCalendarEntry};
use crate::mailbox::{ConnectionAttrs, MailBox, MappedAttrs};
use crate::scheduler::CommsHandle;
use crate::specs::{ApplicationNode, ProvisionedNode};
use crate::HardwareSpecType;
use crate::LinkConfiguration;
use crate::NodeIndex;
use crate::SystemContext;
use crate::SystemSimulationCallbacks;
use crate::{Application, Connection, Service};
use crate::{FramingLead, FrequencyFactor};
use crate::{HardwareSystemSimulation, SystemSimulationTrait};
use crate::{InputFrameRef, LoopbackRef, OutputFrameRef};
use crate::{LinkSpec, NodeSpec};
use crate::{Port, PortLabel, PortProperties};

use anyhow;
use bits::*;
use bits_derive::Bits;
use bitvec::bitbox;
use itertools::Itertools;
use petgraph::adj::List;
use petgraph::algo::min_spanning_tree;
use petgraph::data::Element;
use petgraph::graph::node_index;
use petgraph::prelude::*;
use petgraph::visit::EdgeRef;
use std::collections::HashMap;
use std::convert::TryInto;
use std::fmt;
use std::rc::Rc;

/// The states of a node following the bootstrap protocol
#[derive(Bits, Clone, Copy, Debug, PartialEq)]
enum State {
    /// All nodes start here and send START messages to their neighbors.
    START,
    /// Propagating the topology view.
    PROPAGATE,
    /// A node has received enough info to identify its parent in the spanning tree.
    DISCOVERED,
    /// All nodes have received the topology. Waiting for apps to load.
    READY,
}

// -------------- Connection matrix ----------------------
#[derive(Bits, Clone, Copy, PartialEq)]
struct ConnectionMatrix<const NODES: usize> {
    matrix: [[bool; NODES]; NODES],
}

impl<const NODES: usize> Default for ConnectionMatrix<NODES> {
    fn default() -> Self {
        let row = [false; NODES];
        Self {
            matrix: [row.clone(); NODES],
        }
    }
}

impl<const NODES: usize> fmt::Debug for ConnectionMatrix<NODES> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.matrix.iter().for_each(|row| {
            writeln!(f, "[{}]", row.iter().map(|x| *x as u8).format(", "))
                .expect("Failed to write!");
        });
        write!(f, "")
    }
}

impl<const NODES: usize> ConnectionMatrix<NODES> {
    /// Add a connection between src and dst and return true.
    /// If the connection was present, return false.
    fn add_connection(&mut self, src: NodeIndex, dst: NodeIndex) -> bool {
        if !self.matrix[src.index()][dst.index()] {
            self.matrix[src.index()][dst.index()] = true;
            self.matrix[dst.index()][src.index()] = true;
            true
        } else {
            false
        }
    }

    fn join(&mut self, other: &ConnectionMatrix<NODES>) {
        self.matrix.iter_mut().enumerate().for_each(|(i, row)| {
            row.iter_mut().enumerate().for_each(move |(j, col)| {
                *col = *col | other.matrix[i][j];
            });
        });
    }

    fn spanning_tree(&self) -> Vec<(NodeIndex, NodeIndex)> {
        let mut graph = List::<usize>::new();
        // keep my own map of petgraph::adj::List indices to original node indices. the
        // petgraph list does not support nodes with weights.
        let mut node_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();
        let mut index_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();
        self.matrix.iter().enumerate().for_each(|(id, row)| {
            let node = if row.iter().any(|c| *c) {
                let node_id = if let Some(v) = index_map.get(&node_index(id)) {
                    v.index() as u32
                } else {
                    let o = graph.add_node();
                    node_map.insert(o.into(), node_index(id));
                    index_map.insert(node_index(id), o.into());
                    o
                };
                Some(node_id)
            } else {
                None
            };
            row.iter().enumerate().for_each(|(n, c)| {
                if *c {
                    let other = if let Some(v) = index_map.get(&node_index(n)) {
                        v.index() as u32
                    } else {
                        let o = graph.add_node();
                        node_map.insert(o.into(), node_index(n));
                        index_map.insert(node_index(n), o.into());
                        o
                    };
                    // favor edges directed from smaller indices
                    let weight = if node.unwrap() < other { 1 } else { 2 };
                    graph.add_edge(node.unwrap(), other, weight);
                }
            });
        });
        log::trace!("SP graph: {:?}", petgraph::dot::Dot::new(&graph));
        let edges = min_spanning_tree(&graph)
            .filter_map(|elem| match elem {
                Element::Node { .. } => None,
                Element::Edge { source, target, .. } => {
                    Some((node_map[&node_index(source)], node_map[&node_index(target)]))
                }
            })
            .collect::<Vec<(_, _)>>();
        log::debug!(
            "conn_matrix:\n{:?}\nspanning tree:\n{:?}",
            self,
            edges.iter().format(", ")
        );
        edges
    }
}

/// Packets: the contents of the messages exchanged
///
/// They include the id of the node sending the packets, the current state of
/// the topology (adjacency matrix) and the type of message.
#[derive(Bits, Clone, Copy)]
struct Packet<const NODES: usize> {
    src_id: u64,
    conn_matrix: ConnectionMatrix<NODES>,
    msg: State, // nodes send their current state as a message.
}

impl<const NODES: usize> Packet<NODES> {
    fn src_id(&self) -> NodeIndex {
        node_index(self.src_id as usize)
    }
}

impl<const NODES: usize> fmt::Debug for Packet<NODES> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "src:{} {:?}, conn matrix:\n{:?}",
            self.src_id, self.msg, self.conn_matrix
        )
    }
}

#[derive(Bits, Clone, Copy, Debug)]
struct Neighbor {
    id: u64,
    port: u32,
    state: Option<State>,
}

// --------------------- Node (in aegir) -----------------------------------

/// A node is parametrized with the maximum number of nodes in the topology and
/// the maximum number of conections. These are required to define static
/// structures for serialization into Bits as Nodes are persistent as state for
/// bootstrap actions.
#[derive(Bits, Clone, Copy, Debug)]
struct Node<const NODES: usize, const LINKS: usize> {
    id: u64,
    state: State,
    num_inputs: u32,
    num_outputs: u32,
    /// a list of neighbors, what port are they connected to and their state.
    neighbors: [Option<Neighbor>; LINKS],
    /// store the connection matrix so that we can peek at it in app state
    conn_matrix: ConnectionMatrix<NODES>,
}

impl<const NODES: usize, const LINKS: usize> Default for Node<NODES, LINKS> {
    fn default() -> Self {
        Self {
            id: 0,
            num_inputs: 0,
            num_outputs: 0,
            state: State::START,
            neighbors: [None; LINKS],
            conn_matrix: ConnectionMatrix::<NODES>::default(),
        }
    }
}

impl<const NODES: usize, const LINKS: usize> Node<NODES, LINKS> {
    fn id(&self) -> NodeIndex {
        node_index(self.id as usize)
    }

    /// determine whether we are ready to transition to a new state
    /// condition 0 (terminal node): we have a single port, so only a link to our parent.
    /// condition 1: depending on state, we look to see the status of our neighbors.
    fn ready_to_transition(&self, topology_changed: bool, children: &[usize]) -> bool {
        if self.neighbors.iter().filter(|n| n.is_some()).count() != self.num_inputs as usize {
            // we have not yet heard from all the neigbors
            log::trace!("not ready to transition");
            false
        } else if self.num_inputs == 1 {
            log::trace!("terminal by definition; transition");
            true
        } else {
            let is_transition = match self.state {
                State::START => {
                    self.neighbors
                        .iter()
                        .filter(|&n| n.is_some() && n.unwrap().state.is_some())
                        .count()
                        == self.num_inputs as usize
                } // need to hear from all neighbors
                State::PROPAGATE => {
                    // if there is a cycle in the graph, we need to look at
                    // whether we're getting any new info from our neighbors
                    !topology_changed ||
                    // all the nodes but the parent have been discovered
                    // note that at this point in time we don't know who our
                    // parent is, so we just assume there is one.
                    self.neighbors
                        .iter()
                        .filter(|&n| n.is_some() && n.unwrap().state == Some(State::DISCOVERED))
                        .count()
                        == (self.num_inputs - 1) as usize
                }
                State::DISCOVERED => {
                    // if we are in the DISCOVERED state, we computed a
                    // spanning tree over the current topology, so we have
                    // identified a set of nodes as children. Thus we can
                    // check that all of them are ready.
                    children.iter().all(|&child| {
                        let child_state = self.neighbors[child].unwrap().state.unwrap();
                        child_state == State::DISCOVERED || child_state == State::READY
                    })
                }
                // we should be always ready to transition back to PROPAGATE if any event
                // (add/remove/failure) occurs.
                State::READY => true,
            };
            log::debug!(
                "Node {} topology_changed {} is ready to transition? {}",
                self.id().index(),
                topology_changed,
                is_transition
            );
            is_transition
        }
    }

    fn is_bootstrapped(&self) -> bool {
        self.state == State::READY
    }

    fn process_message(&mut self, port: usize, packet: Packet<NODES>) {
        let prev_state = self.state; // save previous state for logging

        log::debug!(
            "Node {} port: {}, INPUT PACKET: {:?}",
            self.id().index(),
            port,
            packet
        );
        assert_ne!(self.id, packet.src_id); // no self links!

        // TODO(chrispearce): check packets for corruption or malicious behavior.

        // update our connection matrix with the latest info from the neighbors
        // and make sure we add ourselves too
        if self.conn_matrix.add_connection(self.id(), packet.src_id()) {
            // we discovered a neighbor
            self.neighbors[port] = Some(Neighbor {
                id: packet.src_id,
                port: port as u32,
                state: Some(packet.msg),
            });
        }
        let topology_changed = self.conn_matrix != packet.conn_matrix;
        self.conn_matrix.join(&packet.conn_matrix);

        log::debug!(
            "Node {}: neighbors: [{:?}]",
            self.id,
            self.neighbors.iter().format(", "),
        );

        // update the status of the neighbor
        if let Some(mut neighbor) = self.neighbors[port].as_mut() {
            neighbor.state = Some(packet.msg);
        } else {
            panic!("Invalid neighbor {} on port {}", packet.src_id, port);
        }

        // compute the spanning tree

        // a list of the node's children in the spanning tree as indices in
        // the neighbors array.
        let mut children = Vec::new();
        let mut parent = None;
        if self.state == State::DISCOVERED {
            let mst = self.conn_matrix.spanning_tree();
            mst.iter().for_each(|(src, dst)| {
                if self.id() == *src {
                    // find the dst neighbor index
                    if let Some((idx, _n)) = self
                        .neighbors
                        .iter()
                        .enumerate()
                        .find(|(_, n)| n.is_some() && n.unwrap().id == dst.index() as u64)
                    {
                        children.push(idx);
                    }
                }
                if self.id() == *dst {
                    // find the src neighbor id
                    if let Some(n) = self
                        .neighbors
                        .iter()
                        .find(|n| n.is_some() && n.unwrap().id == src.index() as u64)
                    {
                        parent = Some(n.unwrap().id);
                    }
                }
            });
            log::debug!(
                "Node {} parent {:?}, children: {:?}",
                self.id,
                parent,
                children
                    .iter()
                    .map(|child| (child, self.neighbors[*child].unwrap().id))
                    .format(", ")
            );
        }

        // compute what state we need to transition to
        if self.ready_to_transition(topology_changed, &children) {
            self.state = match self.state {
                State::START => State::PROPAGATE,
                State::PROPAGATE => State::DISCOVERED,
                State::DISCOVERED => {
                    if let Some(parent_id) = parent {
                        let mut new_state = State::DISCOVERED;
                        // Waiting for my parent to give me the complete topology
                        if packet.msg == State::READY && parent_id == packet.src_id {
                            new_state = State::READY;
                        }
                        new_state
                    } else {
                        // I'm a root in the spanning tree and I have the _complete_ topology.
                        // I'm transitioning to broadcasting the topology down the tree.
                        State::READY
                    }
                }
                State::READY => {
                    match packet.msg {
                        // if a node suddenly appears, it sends START
                        State::START => State::PROPAGATE,
                        // if something changed in the topology, we need to go back
                        // to propagation and discovery.
                        State::PROPAGATE => {
                            if topology_changed {
                                State::PROPAGATE
                            } else {
                                State::READY
                            }
                        }
                        // otherwise we stay READY
                        _ => State::READY,
                    }
                }
            }
        }

        log::info!(
            "\nNode {}:{:?} received {:?} from {} -> {:?}",
            self.id,
            prev_state,
            packet.msg,
            packet.src_id,
            self.state,
        );
    }

    fn send_messages(&self) -> Vec<Option<Packet<NODES>>> {
        let packet = Packet {
            src_id: self.id,
            conn_matrix: self.conn_matrix,
            msg: self.state,
        };
        log::info!("Node {} sending: {:?}", self.id, packet.msg);
        if self.state == State::START {
            // when we are in the start state, we may have not received any packets to
            // trigger adding neighbors, so we send START on all links.
            (0..self.num_outputs)
                .map(|_| Some(packet.clone()))
                .collect::<Vec<_>>()
        } else {
            let mut outputs = (0..self.num_outputs).map(|_| None).collect::<Vec<_>>();
            self.neighbors
                .iter()
                .filter(|&n| n.is_some())
                .for_each(|n| {
                    outputs[n.unwrap().port as usize] = Some(packet.clone());
                });
            outputs
        }
    }
}

/// the function running the bootstrap protocol
///
/// this function should run continuously on the management unit of each node
/// since it uses the same protocol to discover topology changes (nodes joining
/// or leaving, failures, etc.)
fn bootstrap_action<const NODES: usize, const LINKS: usize>(
    state: LoopbackRef,
    inputs: &[InputFrameRef],
    outputs: &mut [OutputFrameRef],
    _sys: &dyn SystemContext,
) {
    // unpack the local state: where we count the number of invocations.
    let state_bits = &mut state.unwrap_or_else(|| panic!("No state set for bootstrap"));
    let mut node_state = Node::<NODES, LINKS>::unpack(state_bits.as_bitslice());

    // Parse the input packets and compute the new transition state
    inputs.iter().enumerate().for_each(|(port, input)| {
        if let Some(bits) = input {
            if let Some(packet) = <Option<Packet<NODES>>>::unpack(bits) {
                node_state.process_message(port, packet);
            }
        };
    });

    // serialize the output
    node_state
        .send_messages()
        .iter()
        .enumerate()
        .for_each(|(port, pkt)| {
            if pkt.is_some() {
                pkt.pack_to(&mut outputs[port].data);
                outputs[port].valid = true;
            } else {
                outputs[port].valid = false;
            }
        });
    node_state.pack_to(state_bits);
}

/// build the bootstrap application graph that corresponds to a hardware topology.
///   - each node's action function runs the protocol. Node state is maintained
///   by a Node object.
///   - there are connections for every link, sized to Packet sizes.
///
/// returns the application graph and the mapping of system nodes to app nodes.
///
/// TODO(cascaval): remove the requirement that the connection matrix is a fixed
/// sized struct.
fn build_app<const NODES: usize, const LINKS: usize, const BUFFERING: Buffering>(
    topo: &HardwareSpecType<BUFFERING>,
) -> (Application, HashMap<NodeIndex, NodeIndex>) {
    assert!(
        topo.iter_nodes().count() <= NODES,
        "the specified topology is too large"
    );

    if topo.switch_nodes().iter().count() > 0 {
        unimplemented!("bootstrapping for switch nodes is not yet implemented");
    }

    let mut app_spec = Application::new();
    // map (and reverse map) the index of the application node to the hardware node
    let mut app_to_sys: HashMap<NodeIndex, NodeIndex> = HashMap::new();
    let mut sys_to_app: HashMap<NodeIndex, NodeIndex> = HashMap::new();

    let all_nodes = topo
        .iter_nodes()
        .map(|n| {
            let (n_inputs, n_outputs) = topo.get_node_inout_count(n);

            let mut node_state = bitbox![0; <Node<NODES, LINKS> as bits::Bits>::SIZE];
            Node::<NODES, LINKS> {
                id: n.index() as u64,
                num_inputs: n_inputs as u32,
                num_outputs: n_outputs as u32,
                ..Default::default()
            }
            .pack_to(&mut node_state);

            log::debug!(
                "ADDING node: id={}, ports=({}, {})",
                n.index(),
                n_inputs,
                n_outputs
            );
            let node_id = app_spec.add_node(Service::new(
                topo.get_node(n).as_ref().borrow().name(),
                bootstrap_action::<NODES, LINKS>,
                Some(node_state),
                FrequencyFactor(1),
            ));
            app_to_sys.insert(node_id, n);
            sys_to_app.insert(n, node_id);
            node_id
        })
        .collect::<Vec<_>>();

    let frame_size = <Option<Packet<NODES>> as Bits>::SIZE;
    // std::mem::size_of::<Option<Packet<NODES>>>() * 8; // in bits
    let mut port_properties: HashMap<NodeIndex, Vec<_>> = HashMap::new();
    // add the connections
    all_nodes.iter().for_each(|node_id| {
        let (n_inputs, _n_outputs) = topo.get_node_inout_count(app_to_sys[node_id]);

        // Every node adds only its output links. Input links are added by its peer.
        topo.get_output_links(*app_to_sys.get(&node_id).unwrap())
            .for_each(|link_id| {
                let sys_link = topo.get_link(link_id.id());
                let (src_node, dst_node) = topo.get_link_endpoints(link_id.id());
                assert!(src_node == *node_id);

                let dst_props = port_properties
                    .entry(sys_to_app[&dst_node])
                    .or_insert(Vec::new());
                let dst_port_index: usize = sys_link.dst_port().into();
                let dst_port_props = PortProperties {
                    direction: Direction::Incoming,
                    index: dst_port_index,
                    frame_size: frame_size.into(),
                    ..PortProperties::default()
                };
                let dst_port = Port::new(dst_port_index, &dst_port_props);
                dst_props.push((PortLabel::from(dst_port_index), dst_port_props));

                let src_props = port_properties
                    .entry(sys_to_app[&src_node])
                    .or_insert(Vec::new());
                let src_port_index: usize = sys_link.src_port().into();
                let src_port_props = PortProperties {
                    direction: Direction::Outgoing,
                    index: src_port_index,
                    frame_size: frame_size.into(),
                    ..PortProperties::default()
                };
                let src_port = Port::new(src_port_index, &src_port_props);
                // label the output ports after the input ports (port labels must be unique)
                src_props.push((PortLabel::from(src_port_index + n_inputs), src_port_props));

                // and finally add the link
                app_spec.link_simplex_framing(
                    *node_id,
                    *sys_to_app.get(&dst_node).unwrap(),
                    Connection::new(&src_port, &dst_port),
                    FramingLead::Src,
                );
            });
    });
    all_nodes.iter().for_each(|node_id| {
        app_spec
            .get_node(*node_id)
            .borrow_mut()
            .set_ports_properties(port_properties.get(node_id).unwrap());
    });

    log::debug!("Application:\n{}", app_spec);
    (app_spec, sys_to_app)
}

impl<const BUFFERING: Buffering> HardwareSystemSimulation<BUFFERING> {
    fn make_bootstrap_calendars<const NODES: usize>(
        system_spec: &HardwareSpecType<BUFFERING>,
        app_spec: &Application,
        sys_to_app: &HashMap<NodeIndex, NodeIndex>,
    ) {
        const CYCLES_PER_METACYCLE: usize = 1;

        let msg_size = <Option<Packet<NODES>> as Bits>::SIZE;

        // Calendars
        // TODO(cascaval): need a proper memory address to store and read packets for
        // the protocol -- and yes, I expect it'll need to be dedicated.
        let in_base_addr = 0x0;
        let out_base_addr = 0x0;
        let mut in_calendar = Vec::new();
        let mut out_calendar = Vec::new();
        if BUFFERING == BUFFERING_DOUBLE {
            // compute first => comms do nothing for the even cycles
            in_calendar.push(vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)]);
            out_calendar.push(vec![CalendarEntry::new(None, CYCLES_PER_METACYCLE)]);
        }
        in_calendar.push(vec![CalendarEntry::new(
            Some(in_base_addr),
            CYCLES_PER_METACYCLE,
        )]);
        out_calendar.push(vec![CalendarEntry::new(
            Some(out_base_addr),
            CYCLES_PER_METACYCLE,
        )]);
        let in_calendar = IOCalendarVariant::Input(in_calendar.try_into().unwrap());
        let out_calendar = IOCalendarVariant::Output(out_calendar.try_into().unwrap());

        // accumulators for mailboxes for all links
        let mut inboxes_map = HashMap::new();
        let mut outboxes_map = HashMap::new();

        // assign action functions and calendars from app_spec (the bootstrap firmware)
        // for each node, setup the action, and calendars that have a single
        // entry, sending a single frame of size Option<Packet>.
        for sys_node_id in system_spec.iter_nodes() {
            let sys_node = system_spec.get_node(sys_node_id);
            let app_node_id = *sys_to_app.get(&sys_node_id).unwrap();
            let app_node = app_spec.get_node(app_node_id);
            let svc_handle = ServiceHandle::new(app_spec.id(), app_node_id);

            sys_node
                .borrow_mut()
                .register_app(svc_handle.clone(), Rc::clone(&app_node));

            let mut node_calendar = Vec::new();
            node_calendar.push(vec![NodeCalendarEntry::new(
                Some(svc_handle),
                CYCLES_PER_METACYCLE,
            )]);
            if BUFFERING == BUFFERING_DOUBLE {
                // compute first => compute does nothing for the even cycles
                node_calendar.push(vec![NodeCalendarEntry::new(None, CYCLES_PER_METACYCLE)]);
            }
            let node_calendar = CalendarVariant::Node(node_calendar.try_into().unwrap());

            sys_node.borrow_mut().set_calendar(node_calendar);

            for link in system_spec.get_output_links(sys_node_id) {
                assert_eq!(sys_node_id, link.source());
                let dst_node_id = link.target();
                let (src_port, dst_port) = link.weight().get_ports();

                log::trace!(
                    "set calendars for {}:{} -> {}:{}",
                    link.source().index(),
                    src_port,
                    link.target().index(),
                    dst_port
                );

                sys_node
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_io_calendar(out_calendar.clone(), src_port);
                system_spec
                    .get_node(dst_node_id)
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_io_calendar(in_calendar.clone(), dst_port);

                // mem size in number of frames: 1 since currently the frame size == msg_size
                // TODO(cascaval): update when hw frame size changes
                let memory_size = 1;
                let app_link_id = app_spec
                    .get_output_links(app_node_id)
                    .filter(|conn| conn.weight().src_port() == src_port)
                    .map(|conn| conn.id())
                    .next()
                    .unwrap();

                let (app_src_node, app_dst_node) = app_spec.get_link_endpoints(app_link_id);
                let (app_src_port, app_dst_port) = app_spec.get_link(app_link_id).get_ports();

                // mailboxes
                let inboxes = inboxes_map.entry(link.target()).or_insert(Vec::new());
                inboxes.push(ConnectionAttrs {
                    connection_id: CommsHandle::new(app_spec.id(), app_link_id),
                    message_size: msg_size,
                    service_io_index: app_dst_port.into(),
                    service_name: app_spec
                        .get_node(app_dst_node)
                        .borrow()
                        .name()
                        .to_string()
                        .clone(),
                    mapped_endpoint: Some(MappedAttrs {
                        base_address: Some(in_base_addr as usize),
                        frame_size: link.weight().frame_size(),
                        memory_size,
                        hw_io_index: Some(dst_port.into()),
                    }),
                });
                let outboxes = outboxes_map.entry(link.source()).or_insert(Vec::new());
                outboxes.push(ConnectionAttrs {
                    connection_id: CommsHandle::new(app_spec.id(), app_link_id),
                    message_size: msg_size,
                    service_io_index: app_src_port.into(),
                    service_name: app_spec
                        .get_node(app_src_node)
                        .borrow()
                        .name()
                        .to_string()
                        .clone(),
                    mapped_endpoint: Some(MappedAttrs {
                        base_address: Some(out_base_addr as usize),
                        frame_size: link.weight().frame_size(),
                        memory_size,
                        hw_io_index: Some(src_port.into()),
                    }),
                })
            }
        }

        log::trace!("inboxes: {:#?}", inboxes_map.iter().format("\n\t"));
        log::trace!("outboxes: {:#?}", outboxes_map.iter().format("\n\t"));

        for node_id in system_spec.iter_nodes() {
            system_spec
                .get_node(node_id)
                .borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_mailbox(MailBox {
                    inboxes: inboxes_map.get(&node_id).unwrap().to_vec(),
                    outboxes: outboxes_map.get(&node_id).unwrap().to_vec(),
                });
        }
    }

    fn bootstrap<const NODES: usize>(
        &mut self,
        system_spec: &HardwareSpecType<BUFFERING>,
    ) -> anyhow::Result<ConnectionMatrix<NODES>> {
        // TODO(cascaval): make this a parameter? What is a reasonable value to timeout
        // for bootstrap?
        const BOOTSTRAP_TIMEOUT: usize = 1000;
        // TODO(cascaval): the current frame size equals the packet size, so we can do
        // one frame per cycle. We should break this down into packet frames. Moreover,
        // since the protocol will be running all the time, we need to either dedicate a
        // slice to it and start modeling the management unit. Bandwidth on links will
        // have to be dedicated to management slices.
        const LINKS: usize = 6;

        log::debug!("system spec:\n{}", system_spec.to_graphviz());

        let (app_spec, sys_to_app) = build_app::<NODES, LINKS, BUFFERING>(system_spec);
        Self::make_bootstrap_calendars::<NODES>(&system_spec, &app_spec, &sys_to_app);

        // run the system until it converges
        let mut cycle = 0;
        loop {
            if cycle > BOOTSTRAP_TIMEOUT {
                break;
            }
            log::info!("*************** bootstrap cycle {}", cycle);
            self.simulate_system_one_cycle(system_spec, &mut SystemSimulationCallbacks::default());
            let has_converged = app_spec.iter_nodes().all(|n| {
                let node: Node<NODES, LINKS> = Node::unpack(
                    app_spec
                        .get_node(n)
                        .borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                node.is_bootstrapped()
            });
            if has_converged {
                let origin: Node<NODES, LINKS> = Node::unpack(
                    &app_spec
                        .get_node(NodeIndex::new(0))
                        .borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                log::info!("Topology:\n{:?}", origin.conn_matrix);
                log::info!("Protocol completed in {} cycles", cycle + 1);
                return Ok(origin.conn_matrix.clone());
            }
            cycle += 1;
        }
        return Err(anyhow::anyhow!("Failed to converge after {} cycles", cycle));
    }
}

#[cfg(test)]
mod bootstrap_tests {
    use super::*;
    use crate::calendar::BUFFERING_DOUBLE;
    use crate::hw::config::NodeConfiguration;
    use crate::hw::config::SwitchConfiguration;
    use crate::FailureProperties;
    use petgraph::graph::node_index;
    use std::convert::TryInto;

    #[test]
    fn test_conn_matrix_join() {
        const TEST_NUM_NODES: usize = 4;
        let mut c1 = ConnectionMatrix::<TEST_NUM_NODES> {
            matrix: [
                vec![true, false, true, false].try_into().unwrap(),
                vec![false, true, false, true].try_into().unwrap(),
                vec![false, false, false, false].try_into().unwrap(),
                vec![true, true, true, true].try_into().unwrap(),
            ],
        };

        let c2 = ConnectionMatrix::<TEST_NUM_NODES> {
            matrix: [
                vec![true, true, true, false].try_into().unwrap(),
                vec![false, true, false, true].try_into().unwrap(),
                vec![true, false, true, false].try_into().unwrap(),
                vec![false, false, false, false].try_into().unwrap(),
            ],
        };
        c1.join(&c2);
        assert_eq!(c1.matrix[0].to_vec(), vec![true, true, true, false]);
        assert_eq!(c1.matrix[1].to_vec(), vec![false, true, false, true]);
        assert_eq!(c1.matrix[2].to_vec(), vec![true, false, true, false]);
        assert_eq!(c1.matrix[3].to_vec(), vec![true, true, true, true]);
    }
    #[test]
    fn test_conn_matrix_default() {
        const TEST_NUM_NODES: usize = 4;

        let mut c1 = ConnectionMatrix::<TEST_NUM_NODES>::default();
        let c2 = ConnectionMatrix::<TEST_NUM_NODES> {
            matrix: [
                vec![true, false, true, false].try_into().unwrap(),
                vec![false, true, false, true].try_into().unwrap(),
                vec![false, false, false, false].try_into().unwrap(),
                vec![true, true, true, true].try_into().unwrap(),
            ],
        };
        c1.join(&c2);
        assert_eq!(c1, c2);
    }

    #[test]
    fn test_spanning_tree() {
        let _logger = env_logger::builder().try_init();
        let line = ConnectionMatrix::<4> {
            matrix: [
                vec![false, false, true, false].try_into().unwrap(),
                vec![false, false, false, false].try_into().unwrap(),
                vec![true, false, false, false].try_into().unwrap(),
                vec![false, false, false, false].try_into().unwrap(),
            ],
        };
        let st = line.spanning_tree();
        log::info!(
            "conn_matrix:\n{:?}\nspanning tree:\n{:?}",
            line,
            st.iter().format(", ")
        );
        assert_eq!(st.iter().count(), 1);

        let mesh = ConnectionMatrix::<4> {
            matrix: [
                vec![false, true, true, false].try_into().unwrap(),
                vec![true, false, false, true].try_into().unwrap(),
                vec![true, false, false, true].try_into().unwrap(),
                vec![false, true, true, false].try_into().unwrap(),
            ],
        };
        let st = mesh.spanning_tree();
        log::info!(
            "conn_matrix:\n{:?}\nspanning tree:\n{:?}",
            mesh,
            st.iter().format(", ")
        );
        assert_eq!(st.iter().count(), 3);

        let full = ConnectionMatrix::<4> {
            matrix: [
                vec![false, true, true, true].try_into().unwrap(),
                vec![true, false, true, true].try_into().unwrap(),
                vec![true, true, false, true].try_into().unwrap(),
                vec![true, true, true, false].try_into().unwrap(),
            ],
        };
        let st = full.spanning_tree();
        log::info!(
            "conn_matrix:\n{:?}\nspanning tree:\n{:?}",
            full,
            st.iter().format(", ")
        );
        assert_eq!(st.iter().count(), 3);

        let tree = ConnectionMatrix::<7> {
            matrix: [
                vec![false, true, true, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![true, false, false, true, true, false, false]
                    .try_into()
                    .unwrap(),
                vec![true, false, false, false, false, true, true]
                    .try_into()
                    .unwrap(),
                vec![false, true, false, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![false, true, false, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![false, false, true, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![false, false, true, false, false, false, false]
                    .try_into()
                    .unwrap(),
            ],
        };
        let st = tree.spanning_tree();
        log::info!(
            "conn_matrix:\n{:?}\nspanning tree:\n{:?}",
            tree,
            st.iter().format(", ")
        );
        assert_eq!(st.iter().count(), 6);
        assert!(st.iter().contains(&(node_index(0), node_index(1))));
        assert!(st.iter().contains(&(node_index(0), node_index(2))));
        assert!(st.iter().contains(&(node_index(1), node_index(3))));
        assert!(st.iter().contains(&(node_index(1), node_index(4))));
        assert!(st.iter().contains(&(node_index(2), node_index(5))));
        assert!(st.iter().contains(&(node_index(2), node_index(6))));
    }

    #[test]
    fn test_mesh() {
        use crate::hw::topologies::mesh;

        let _ = env_logger::try_init();
        const NUM_NODES: usize = 4;
        let (x, y) = (2, 2);

        let topo = mesh::<{ BUFFERING_DOUBLE }>(
            &[x, y],
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration {
                calendar_size: 1,
                frame_size: <Option<Packet<NUM_NODES>> as Bits>::SIZE,
                ..Default::default()
            },
        );
        let mut simulation = HardwareSystemSimulation::<{ BUFFERING_DOUBLE }>::new(
            &topo,
            FailureProperties::default(),
        );
        let conn_matrix = simulation.bootstrap::<NUM_NODES>(&topo);
        assert!(conn_matrix.is_ok());
        let expected_matrix = ConnectionMatrix::<NUM_NODES> {
            matrix: [
                vec![false, true, true, false].try_into().unwrap(),
                vec![true, false, false, true].try_into().unwrap(),
                vec![true, false, false, true].try_into().unwrap(),
                vec![false, true, true, false].try_into().unwrap(),
            ],
        };
        assert_eq!(conn_matrix.unwrap(), expected_matrix);
    }

    #[test]
    fn test_line() {
        use crate::hw::topologies::line;

        let _ = env_logger::try_init();
        const NUM_NODES: usize = 13;
        let topo = line::<{ BUFFERING_DOUBLE }>(
            NUM_NODES,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration {
                calendar_size: 1,
                frame_size: <Option<Packet<NUM_NODES>> as Bits>::SIZE,
                ..Default::default()
            },
        );
        let mut simulation = HardwareSystemSimulation::<{ BUFFERING_DOUBLE }>::new(
            &topo,
            FailureProperties::default(),
        );
        let conn_matrix = simulation.bootstrap::<NUM_NODES>(&topo);
        assert!(conn_matrix.is_ok());
        let conn_matrix = conn_matrix.unwrap();
        (0..NUM_NODES).for_each(|row| {
            conn_matrix.matrix[row]
                .iter()
                .enumerate()
                .for_each(|(col, &val)| {
                    assert_eq!(
                        val,
                        (row > 0 && col == row - 1) || (row < NUM_NODES && col == row + 1)
                    );
                });
        });
    }

    #[test]
    fn test_full() {
        use crate::hw::topologies::fully_connected;
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 6;
        let topo = fully_connected::<{ BUFFERING_DOUBLE }>(
            NUM_NODES,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration {
                calendar_size: 1,
                frame_size: <Option<Packet<NUM_NODES>> as Bits>::SIZE,
                ..Default::default()
            },
        );
        let mut simulation = HardwareSystemSimulation::<{ BUFFERING_DOUBLE }>::new(
            &topo,
            FailureProperties::default(),
        );
        let conn_matrix = simulation.bootstrap::<NUM_NODES>(&topo);
        assert!(conn_matrix.is_ok());
        let conn_matrix = conn_matrix.unwrap();
        (0..NUM_NODES).for_each(|row| {
            conn_matrix.matrix[row]
                .iter()
                .enumerate()
                .for_each(|(col, &val)| {
                    // each node is connected to everyone else but itself.
                    assert_eq!(val, row != col);
                });
        });
    }

    #[test]
    fn test_hypercube() {
        use crate::hw::topologies::hypercube;
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 16;
        let degree = 4;
        let topo = hypercube::<{ BUFFERING_DOUBLE }>(
            degree,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration {
                calendar_size: 1,
                frame_size: <Option<Packet<NUM_NODES>> as Bits>::SIZE,
                ..Default::default()
            },
        );
        let mut simulation = HardwareSystemSimulation::<{ BUFFERING_DOUBLE }>::new(
            &topo,
            FailureProperties::default(),
        );
        let conn_matrix = simulation.bootstrap::<NUM_NODES>(&topo);
        assert!(conn_matrix.is_ok());
        let conn_matrix = conn_matrix.unwrap();
        (0..NUM_NODES).for_each(|row| {
            assert_eq!(
                conn_matrix.matrix[row]
                    .iter()
                    .map(|c| if *c { 1 } else { 0 })
                    .sum::<usize>(),
                degree
            );
        });
    }

    #[test]
    fn test_torus3d() {
        use crate::hw::topologies::torus;
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 64;
        let (x, y, z) = (4, 4, 4);
        let topo = torus::<{ BUFFERING_DOUBLE }>(
            &[x, y, z],
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration {
                calendar_size: 1,
                frame_size: <Option<Packet<NUM_NODES>> as Bits>::SIZE,
                ..Default::default()
            },
        );
        let mut simulation = HardwareSystemSimulation::<{ BUFFERING_DOUBLE }>::new(
            &topo,
            FailureProperties::default(),
        );
        let conn_matrix = simulation.bootstrap::<NUM_NODES>(&topo);
        assert!(conn_matrix.is_ok());
        let conn_matrix = conn_matrix.unwrap();
        (0..(x * y * z) - 1).for_each(|row| {
            assert_eq!(
                conn_matrix.matrix[row]
                    .iter()
                    .map(|c| if *c { 1 } else { 0 })
                    .sum::<usize>(),
                6
            );
        });
    }

    #[test]
    #[should_panic(expected = "not implemented: bootstrapping for switch nodes")]
    fn test_star() {
        use crate::hw::topologies::star;
        let _ = env_logger::try_init();
        const NUM_HOSTS: usize = 6;
        const NUM_NODES: usize = NUM_HOSTS + 1;
        let topo = star::<{ BUFFERING_DOUBLE }>(
            NUM_HOSTS,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration {
                calendar_size: 1,
                frame_size: <Option<Packet<NUM_NODES>> as Bits>::SIZE,
                ..Default::default()
            },
        );
        let mut simulation = HardwareSystemSimulation::<{ BUFFERING_DOUBLE }>::new(
            &topo,
            FailureProperties::default(),
        );
        let conn_matrix = simulation.bootstrap::<NUM_NODES>(&topo);
        assert!(conn_matrix.is_ok());
        let conn_matrix = conn_matrix.unwrap();
        conn_matrix.matrix[0]
            .iter()
            .enumerate()
            .for_each(|(col, &val)| {
                assert_eq!(val, col > 0);
            });
        (1..NUM_NODES).for_each(|row| {
            conn_matrix.matrix[row]
                .iter()
                .enumerate()
                .for_each(|(col, &val)| {
                    assert_eq!(val, col == 0);
                });
        });
    }

    #[test]
    #[should_panic(expected = "not implemented: bootstrapping for switch nodes")]
    fn test_tree() {
        use crate::hw::topologies::tree;
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 7;
        let (height, children) = (3, 2);
        let topo = tree::<{ BUFFERING_DOUBLE }>(
            height,
            children,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration {
                calendar_size: 1,
                frame_size: <Option<Packet<NUM_NODES>> as Bits>::SIZE,
                ..Default::default()
            },
        );
        let mut simulation = HardwareSystemSimulation::<{ BUFFERING_DOUBLE }>::new(
            &topo,
            FailureProperties::default(),
        );
        let conn_matrix = simulation.bootstrap::<NUM_NODES>(&topo);
        assert!(conn_matrix.is_ok());
        let expected_matrix = ConnectionMatrix::<NUM_NODES> {
            matrix: [
                vec![false, true, true, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![true, false, false, true, true, false, false]
                    .try_into()
                    .unwrap(),
                vec![true, false, false, false, false, true, true]
                    .try_into()
                    .unwrap(),
                vec![false, true, false, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![false, true, false, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![false, false, true, false, false, false, false]
                    .try_into()
                    .unwrap(),
                vec![false, false, true, false, false, false, false]
                    .try_into()
                    .unwrap(),
            ],
        };
        assert_eq!(conn_matrix.unwrap(), expected_matrix);
    }
}
