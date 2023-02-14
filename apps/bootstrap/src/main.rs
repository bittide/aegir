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

/// The protocol is documented in [Bootstrap Design V2](../../../docs/bootstrap-v2.pdf).
///
use anyhow;
use bits::*;
use bits_derive::Bits;
use bitvec::bitbox;
use itertools::Itertools;
use petgraph::adj::{List, NodeIndex};
use petgraph::algo::min_spanning_tree;
use petgraph::data::Element;
use platform::specs::ApplicationNode;
use platform::Application;
use platform::NodeSpec;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;
use rand::Rng;
use std::collections::HashMap;
use std::convert::TryInto;
use structopt::StructOpt;
use topology::*;

/// The states of a node following the bootstrap protocol
#[derive(Bits, Clone, Copy, Debug, PartialEq)]
enum State {
    START,      // All nodes start here and send START messages to their neighbors
    PROPAGATE,  // Propagating the topology view
    DISCOVERED, // A node has received enough info to identify its parent in the spanning tree
    READY,      // All nodes have received the topology. Waiting for apps to load.
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

impl<const NODES: usize> std::fmt::Debug for ConnectionMatrix<NODES> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.matrix.iter().for_each(|row| {
            writeln!(
                f,
                "[{}]",
                row.iter().map(|x| if *x { 1 } else { 0 }).format(", ")
            )
            .expect("Failed to write!");
        });
        write!(f, "")
    }
}

impl<const NODES: usize> ConnectionMatrix<NODES> {
    /// Add a connection between src and dst and return true.
    /// If the connection was present, return false.
    fn add_connection(&mut self, src: usize, dst: usize) -> bool {
        if !self.matrix[src][dst] {
            self.matrix[src][dst] = true;
            self.matrix[dst][src] = true;
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

    fn spanning_tree(&self) -> Vec<(NodeId, NodeId)> {
        let mut graph = List::<usize>::new();
        // keep my own map of petgraph::adj::List indices to original node indices. the
        // petgraph list does not support nodes with weights.
        let mut node_map: HashMap<NodeIndex, NodeId> = HashMap::new();
        let mut index_map: HashMap<NodeId, NodeIndex> = HashMap::new();
        self.matrix.iter().enumerate().for_each(|(id, row)| {
            let node = if row.iter().any(|c| *c) {
                let node_id = if let Some(v) = index_map.get(&id) {
                    *v
                } else {
                    let o = graph.add_node();
                    node_map.insert(o, id);
                    index_map.insert(id, o);
                    o
                };
                Some(node_id)
            } else {
                None
            };
            row.iter().enumerate().for_each(|(n, c)| {
                if *c {
                    let other = if let Some(v) = index_map.get(&n) {
                        *v
                    } else {
                        let o = graph.add_node();
                        node_map.insert(o, n);
                        index_map.insert(n, o);
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
                    Some((node_map[&(source as u32)], node_map[&(target as u32)]))
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
    fn src_id(&self) -> NodeId {
        self.src_id as NodeId
    }
}

impl<const NODES: usize> std::fmt::Debug for Packet<NODES> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
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
/// waves actions.
#[derive(Bits, Clone, Copy, Debug)]
struct Node<const NODES: usize, const LINKS: usize> {
    id: u64,
    state: State,
    num_ports: u32,
    /// a list of neighbors, what port are they connected to and their state.
    neighbors: [Option<Neighbor>; LINKS],
    /// store the connection matrix so that we can peek at it in app state
    conn_matrix: ConnectionMatrix<NODES>,
}

impl<const NODES: usize, const LINKS: usize> Default for Node<NODES, LINKS> {
    fn default() -> Self {
        Self {
            id: 0,
            num_ports: 0,
            state: State::START,
            neighbors: [None; LINKS],
            conn_matrix: ConnectionMatrix::<NODES>::default(),
        }
    }
}

impl<const NODES: usize, const LINKS: usize> topology::Vertex for Node<NODES, LINKS> {
    fn new_vertex() -> Self {
        Node::default()
    }
    fn id(&self) -> NodeId {
        self.id as usize
    }
    fn set_id(&mut self, id: NodeId) {
        self.id = id as u64;
    }
}

impl<const NODES: usize, const LINKS: usize> Node<NODES, LINKS> {
    /// determine whether we are ready to transition to a new state
    /// condition 0 (terminal node): we have a single port, so only a link to our parent.
    /// condition 1: depending on state, we look to see the status of our neighbors.
    fn ready_to_transition(&self, topology_changed: bool, children: &[usize]) -> bool {
        if self.neighbors.iter().filter(|n| n.is_some()).count() != self.num_ports as usize {
            // we have not yet heard from all the neigbors
            log::debug!("not yet");
            false
        } else if self.num_ports == 1 {
            log::debug!("terminal by def");
            true
        } else {
            let is_transition = match self.state {
                State::START => {
                    self.neighbors
                        .iter()
                        .filter(|&n| n.is_some() && n.unwrap().state.is_some())
                        .count()
                        == self.num_ports as usize
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
                        == (self.num_ports - 1) as usize
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
                self.id(),
                topology_changed,
                is_transition
            );
            is_transition
        }
    }

    fn is_done(&self) -> bool {
        self.state == State::READY
    }

    fn process_message(&mut self, port: usize, packet: Packet<NODES>) {
        let prev_state = self.state; // save previous state for logging

        log::debug!("Node {} INPUT PACKET: {:?}", self.id(), packet);
        // TODO(chrispearce): check packets for corruption or malicious behavior.
        assert_ne!(self.id, packet.src_id); // no self links!

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

        // update the status of the neighbor
        if let Some(mut neighbor) = self.neighbors[port].as_mut() {
            neighbor.state = Some(packet.msg);
        } else {
            panic!("Invalid neighbor {}", packet.src_id);
        }
        log::debug!(
            "Node {}: neighbors {:?}",
            self.id(),
            self.neighbors.iter().format(", ")
        );

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
                        .find(|(_, n)| n.is_some() && n.unwrap().id == *dst as u64)
                    {
                        children.push(idx);
                    }
                }
                if self.id() == *dst {
                    // find the src neighbor id
                    if let Some(n) = self
                        .neighbors
                        .iter()
                        .find(|n| n.is_some() && n.unwrap().id == *src as u64)
                    {
                        parent = Some(n.unwrap().id);
                    }
                }
            });
            log::debug!(
                "Node {} parent {:?}, children: {:?}",
                self.id(),
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
                    if parent.is_none() {
                        // I'm a root in the spanning tree and I have the _complete_ topology.
                        // I'm transitioning to broadcasting the topology down the tree.
                        State::READY
                    } else {
                        // Waiting for my parent to give me the complete topology
                        match packet.msg {
                            State::READY => {
                                if parent.is_some() && parent.unwrap() == packet.src_id {
                                    State::READY
                                } else {
                                    State::DISCOVERED
                                }
                            }
                            _ => State::DISCOVERED,
                        }
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
            (0..self.num_ports)
                .map(|_| Some(packet.clone()))
                .collect::<Vec<_>>()
        } else {
            let mut outputs = (0..self.num_ports).map(|_| None).collect::<Vec<_>>();
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

#[derive(Debug)]
struct Connection {
    id: ConnectionId,
    source: NodeId,
    sink: NodeId,
}

impl topology::Edge for Connection {
    fn new_edge(src_node: NodeId, dst_node: NodeId) -> Self {
        Connection {
            id: 0,
            source: src_node,
            sink: dst_node,
        }
    }
    fn id(&self) -> ConnectionId {
        self.id
    }
    fn set_id(&mut self, id: NodeId) {
        self.id = id;
    }

    fn source(&self) -> NodeId {
        self.source
    }
    fn sink(&self) -> NodeId {
        self.sink
    }
}

macro_rules! action_gen {
    ($node_name: ident, $node_id: ident, $app_spec: ident, $num_ports: literal) => {
        waves::action!(&$node_name in $app_spec
            (state: Node<NODES, LINKS>)
            (inputs: [Option<Packet<NODES>>; $num_ports])
            -> (outputs: [Option<Packet<NODES>>; $num_ports])
            {
              let mut data = bitbox![0; <Node<NODES, LINKS> as bits::Bits>::SIZE];
              Node::<NODES, LINKS> {
                  id: $node_id,
                  num_ports: $num_ports,
                  ..Default::default()
              }.pack_to(&mut data);
              data
            }
            {
                // Parse the input packets and compute the new transition state
                inputs.iter().enumerate().for_each(|(port, packet)| {
                    if packet.is_some() {
                        state.process_message(port, packet.unwrap());
                    }
                });

                // send messages to neighbors based on the new state
                outputs = state.send_messages().try_into().unwrap();
            }
        )
    }
}

fn build_app<const NODES: usize, const LINKS: usize>(
    topo: Topology<Node<NODES, LINKS>, Connection>,
) -> Application {
    assert!(
        topo.nodes().count() <= NODES,
        "the specified topology is too large"
    );
    let mut app_spec = Application::new();

    let all_nodes = topo
        .nodes()
        .map(|n| {
            let num_ports: u32 = topo.node_connections(&n.id()).count() as u32;
            log::debug!("ADDING NODES, Node: id={}, ports={}", n.id(), num_ports);
            let node_id = n.id() as u64;
            let node_name = format!("node {} (ports {})", node_id, num_ports);
            match num_ports {
                1 => action_gen!(node_name, node_id, app_spec, 1),
                2 => action_gen!(node_name, node_id, app_spec, 2),
                3 => action_gen!(node_name, node_id, app_spec, 3),
                4 => action_gen!(node_name, node_id, app_spec, 4),
                5 => action_gen!(node_name, node_id, app_spec, 5),
                6 => action_gen!(node_name, node_id, app_spec, 6),
                v => panic!("Please add more arms to handle {} ports", v),
            }
        })
        .collect::<Vec<_>>();

    // a map from node id to port_id, signifying the last port used.
    // TODO(cascaval): do we really need to remap the node ports and then use the
    // port id as an index into the arrays that track the state of the node? Or is
    // there a way to reuse the topology information from System spec to identify
    // the node pairs based on links?
    let mut last_port_used = HashMap::new();
    topo.nodes().for_each(|n| {
        last_port_used.insert(n.id(), 0);
    });

    // map a pair of nodes (src, dst) to a pair of ports (src_port, dst_port).
    // this is needed because the topology we built is undirected, but we want every
    // link to represent a pair of links, and for that we need to remember the
    // mapping we did when we added dst links as part of the src processing.
    // Note: this allows only a pair of links per pair of nodes.
    let mut portmap = HashMap::new();
    for node in all_nodes.iter() {
        let src = node.index();
        for con in topo // for all outgoing connections
            .node_connections(&src)
            .filter(|c| c.source() == src)
        {
            let dst = con.sink();
            let (src_port, dst_port) = if let Some(&(src_port, dst_port)) = portmap.get(&(src, dst))
            {
                (src_port, dst_port)
            } else {
                let src_port = *last_port_used.get(&src).unwrap();
                let dst_port = *last_port_used.get(&dst).unwrap();
                portmap.insert((src, dst), (src_port, dst_port));
                portmap.insert((dst, src), (dst_port, src_port));
                *last_port_used.get_mut(&src).unwrap() += 1;
                *last_port_used.get_mut(&dst).unwrap() += 1;
                (src_port, dst_port)
            };
            // the link represented in the topology con.source() -> dst
            waves::link!(all_nodes[src] outputs[src_port]
                  -> all_nodes[dst] inputs[dst_port] in app_spec);
            // we also need a back link (for response msgs)
            waves::link!(all_nodes[dst] outputs[dst_port]
                  -> all_nodes[src] inputs[src_port] in app_spec);
        }
    }
    log::debug!("{}", app_spec);
    app_spec
}

fn bootstrap<const NODES: usize, const LINKS: usize>(
    cycles: usize,
    origin_index: usize,
    topo: Topology<Node<NODES, LINKS>, Connection>,
) -> anyhow::Result<ConnectionMatrix<NODES>> {
    let app_spec = build_app(topo);
    let mut simulation = platform::SoftwareSystemSimulation::new(&app_spec);
    for c in 0..cycles {
        log::info!("*************** Cycle {}", c);
        simulation.simulate_system_one_cycle(&app_spec, &mut SystemSimulationCallbacks::default());
        let is_done = app_spec.iter_nodes().all(|n| {
            let node: Node<NODES, LINKS> = Node::unpack(
                app_spec
                    .get_node(n)
                    .borrow()
                    .into_stateful_node()
                    .unwrap()
                    .persistent_state()
                    .unwrap(),
            );
            node.is_done()
        });
        if is_done {
            let origin: Node<NODES, LINKS> = Node::unpack(
                &app_spec
                    .get_node(platform::NodeIndex::new(origin_index))
                    .borrow()
                    .into_stateful_node()
                    .unwrap()
                    .persistent_state()
                    .unwrap(),
            );
            log::info!("Topology:\n{:?}", origin.conn_matrix);
            log::info!("Protocol completed in {} cycles", c);
            return Ok(origin.conn_matrix.clone());
        }
    }
    return Err(anyhow::anyhow!(
        "Failed to converge after {} cycles",
        cycles
    ));
}

#[derive(StructOpt)]
struct CmdLine {
    /// origin node
    #[structopt(short = "origin")]
    origin_node: Option<NodeId>,
    /// max number of cycles to simulate
    #[structopt(short = "cycles", default_value = "1000")]
    cycles: usize,
    #[structopt(flatten)]
    topo_options: topology::Options,
}

fn main() {
    env_logger::init();
    const MAX_NUM_NODES: usize = 100;
    const MAX_NUM_LINKS: usize = 10;
    let args = CmdLine::from_args();
    let topo: Topology<Node<MAX_NUM_NODES, MAX_NUM_LINKS>, Connection> =
        args.topo_options.get_topology();

    // Generate a random origin node within topology
    let num_nodes = topo.node_ids().count();
    log::info!("topo size: {}", num_nodes);
    let origin_node_id = args.origin_node.unwrap_or_else(|| {
        let mut rng = rand::thread_rng();
        rng.gen_range(0..num_nodes)
    });
    log::info!("origin_node_id: {}", origin_node_id);
    log::info!("Software simulation");
    bootstrap(args.cycles, origin_node_id, topo).expect("Failed convergence!");
}

#[cfg(test)]
mod tests {
    use super::*;
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
        assert!(st.iter().contains(&(0, 1)));
        assert!(st.iter().contains(&(0, 2)));
        assert!(st.iter().contains(&(1, 3)));
        assert!(st.iter().contains(&(1, 4)));
        assert!(st.iter().contains(&(2, 5)));
        assert!(st.iter().contains(&(2, 6)));
    }

    #[test]
    fn test_mesh() {
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 4;
        const NUM_LINKS: usize = 2;
        let (x, y, origin_node_id) = (2, 2, 2);
        let topo: Topology<Node<NUM_NODES, NUM_LINKS>, Connection> = Mesh::mesh(&[x, y]);
        let conn_matrix = bootstrap(20, origin_node_id, topo);
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
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 4;
        const NUM_LINKS: usize = 2;
        let (n, origin_node_id) = (4, 1);
        let topo: Topology<Node<NUM_NODES, NUM_LINKS>, Connection> = Line::line(n);
        let conn_matrix = bootstrap(20, origin_node_id, topo);
        assert!(conn_matrix.is_ok());
        let expected_matrix = ConnectionMatrix::<NUM_NODES> {
            matrix: [
                vec![false, true, false, false].try_into().unwrap(),
                vec![true, false, true, false].try_into().unwrap(),
                vec![false, true, false, true].try_into().unwrap(),
                vec![false, false, true, false].try_into().unwrap(),
            ],
        };
        assert_eq!(conn_matrix.unwrap(), expected_matrix);
    }
    #[test]
    fn test_full() {
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 4;
        const NUM_LINKS: usize = 3;
        let (n, origin_node_id) = (4, 0);
        let topo: Topology<Node<NUM_NODES, NUM_LINKS>, Connection> = FullyConnected::full(n);
        let conn_matrix = bootstrap(20, origin_node_id, topo);
        assert!(conn_matrix.is_ok());
        let expected_matrix = ConnectionMatrix::<NUM_NODES> {
            matrix: [
                vec![false, true, true, true].try_into().unwrap(),
                vec![true, false, true, true].try_into().unwrap(),
                vec![true, true, false, true].try_into().unwrap(),
                vec![true, true, true, false].try_into().unwrap(),
            ],
        };
        assert_eq!(conn_matrix.unwrap(), expected_matrix);
    }

    #[test]
    fn test_tree() {
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 7;
        const NUM_LINKS: usize = 3;
        let (height, children, origin_node_id) = (3, 2, 0);
        let topo: Topology<Node<NUM_NODES, NUM_LINKS>, Connection> = Tree::tree(height, children);
        let conn_matrix = bootstrap(20, origin_node_id, topo);
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
    #[test]
    fn test_torus3d() {
        let _ = env_logger::try_init();
        const NUM_NODES: usize = 64;
        const NUM_LINKS: usize = 6;
        let (x, y, z, origin_node_id) = (4, 4, 4, 0);
        let topo: Topology<Node<NUM_NODES, NUM_LINKS>, Connection> = Torus::torus(&[x, y, z]);
        let conn_matrix = bootstrap(20, origin_node_id, topo);
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
}
