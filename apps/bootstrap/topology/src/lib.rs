// Copyright 2020 Google LLC
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

//!
//! Topologies are a fundamental feature all connected systems. It is
//! desirable to build them into a library that can be used across different
//! simulation environments. For example Luna requires topologies to
//! evaluate control algorithms. Our inventory management system will
//! require the same topology, but with different nodes and links to
//! simulate availability. Our resource allocation and partitioning system
//! will require yet a different set of nodes and links, connected into
//! similar topologies.
//!
//! Network topologies are represented as a graph of
//! vertices connected by edges. `Vertex` and `Edge` are defined as traits
//! that specify the interface that the nodes and connections of the
//! topology should implement.
//!
//! We define the following topologies: Star, Mesh, Tree, Torus, Hypercube,
//! and FullyConnected. These topologies are minimally defined, only the
//! structure. However, we do define structs to encapsulate the definition
//! of the network topology, such that they could be extended with
//! additional parameters in the future, for example, link latencies or
//! bandwidth, node attributes to build different types of nodes, etc.
//!
//! # Failures
//!
//! See failures module.
//!
//! # Examples
//!
//! ```compile_fail
//! use topology::*;
//! // define Node and Conn structs implementing the Vertex and Edge traits
//! struct Node { ... }
//! impl Vertex for Node { ... }
//! struct Conn { ... }
//! impl Edge for Conn { ... }
//!
//! // build a 3x4 2D mesh
//! let topo: Topology<Node, Conn> = Mesh::mesh(&[3, 4]);
//!
//! // build a custom topology of three nodes
//! let nodes = vec![ Node::new_vertex(), Node::new_vertex(), Node::new_vertex()];
//! let conns = vec![ Conn::new_edge(1, 2), Conn::new_edge(2, 3), Conn::new_edge(1, 3)];
//! let topo: Topology<Node, Conn> = Topology::new_from_vec(nodes, conns, Topologytype::Handcrafted);
//!
//! // iterate through all the nodes in the topology
//! for n in topo.nodes() {
//!     println!("Node: id={}", n.id());
//! }
//!```
//!
//! # TODO
//!
//! - Add support for uuids
//!
//! - Define a generic mechanism to add attributes, such as bandwidth or
//! latency.
//!
//! - In the future it would be helpful to define hierarchical topologies,
//! where clusters of nodes have one of the primitive topologies, and
//! clusters are connected in a different topology.
//!
//! - Would be cool to be able to display the topology object according to
//! the type of the topology it was constructed from, e.g., a 2D mesh as a
//! 2-dimensional grid, etc. However, that's currently beyond my Rust
//! skills.
//!

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;

mod failure;
mod layout;
mod options;

mod full;
mod hypercube;
mod line;
mod mesh;
mod star;
mod torus;
mod tree;

// Re-export useful types
pub use crate::failure::{ElementFailure, MetaCycle, TopologyFailure};
pub use crate::layout::Coordinates;
pub use crate::layout::Layout2D;
pub use crate::options::Options;

// Re-export petgraph iterator types
pub use petgraph::graph::{EdgeIndices, EdgeWeightsMut, Edges, NodeIndices, NodeWeightsMut};
// Re-export the topology builders
pub use crate::full::FullyConnected;
pub use crate::hypercube::Hypercube;
pub use crate::line::Line;
pub use crate::mesh::Mesh;
pub use crate::star::Star;
pub use crate::torus::Torus;
pub use crate::tree::Tree;
use petgraph::graph::{edge_index, node_index};
use petgraph::prelude::*;

/// The type of ids for nodes.
///
pub type NodeId = usize;

/// The type of ids for connections.
///
pub type ConnectionId = usize;

#[derive(Debug, Serialize, Deserialize)]
pub enum TopologyType {
    Full(FullyConnected),
    Hypercube(Hypercube),
    Line(Line),
    Mesh(Mesh),
    Star(Star),
    Torus(Torus),
    Tree(Tree),
    /// A topology that has been constructed manually. Mainly for test.
    Handcrafted,
}

impl TopologyType {
    pub fn name(&self) -> String {
        match self {
            Self::Full(f) => f.name(),
            Self::Hypercube(h) => h.name(),
            Self::Line(l) => l.name(),
            Self::Mesh(m) => m.name(),
            Self::Star(s) => s.name(),
            Self::Torus(t) => t.name(),
            Self::Tree(t) => t.name(),
            Self::Handcrafted => String::from("Handcrafted"),
        }
    }
}

// ----------------- interfaces for the topology elements-------------------
//
/// Interface that needs to be implemented by a Node in the topology.
///
/// The Vertex trait is used by the builder to manage nodes in the
/// topology. The actual implementation of the nodes is expected to
/// encapsulate additional functionality.
pub trait Vertex {
    /// Create a node.
    ///
    /// We do not call this new, so that structs implementing this trait can
    /// have their own new.
    fn new_vertex() -> Self;
    /// Get the node's id.
    fn id(&self) -> NodeId;
    fn set_id(&mut self, id: NodeId);
}

/// Interface that needs to be implemented by a Connection in the topology.
///
/// The Edge trait is used by the builder to manage connections in the
/// topology. The actual implementation of the connections is expected to
/// encapsulate additional functionality.
///
/// Connections are bidirectional, so the source->sink assignation is
/// entirely arbitrary and should not be interpreted as semantically
/// significant.
pub trait Edge {
    /// Create a new connection between `src_node` and `dst_node`.
    ///
    /// We do not call this new, so that structs implementing this trait can
    /// have their own new.
    fn new_edge(src_node: NodeId, dst_node: NodeId) -> Self;
    /// Get the connection's id.
    fn id(&self) -> ConnectionId;
    fn set_id(&mut self, id: ConnectionId);
    /// Get the id of the node at the source end of the connection.
    fn source(&self) -> NodeId;
    /// Get the id of the node at the sink end of the connection.
    fn sink(&self) -> NodeId;
}

/// A topology is represented as a set of nodes and their connections.
///
/// This is common for all topologies and it is returned by the topology
/// builder.  It allows for efficient lookup of nodes and connections than
/// iterating over vectors.
// #[derive(Serialize, Deserialize)]
pub struct Topology<N, C>
where
    N: Vertex,
    C: Edge + Debug,
{
    /// the topology is a petgraph::Graph directed graph.
    topo: Graph<N, C, Undirected>,

    /// the type of topology
    /// A pointer to the builder of the topology, to get additional
    /// information.
    topology_type: TopologyType,
}

impl<N, C> Topology<N, C>
where
    N: Vertex,
    C: Edge + Debug,
{
    pub fn new(topology_type: TopologyType) -> Self {
        Self {
            topo: Graph::<N, C, Undirected>::new_undirected(),
            topology_type,
        }
    }

    /// add a node and set its id in the weight (which is the type of node we defined).
    pub fn add_node(&mut self, node: N) -> NodeId {
        let id = self.topo.add_node(node);
        self.topo.node_weight_mut(id).unwrap().set_id(id.index());
        id.index()
    }

    /// add a link and set its id in the weight (which is the type of edge we defined).
    pub fn add_link(&mut self, link: C) -> ConnectionId {
        let id = self
            .topo
            .add_edge(node_index(link.source()), node_index(link.sink()), link);
        self.topo.edge_weight_mut(id).unwrap().set_id(id.index());
        id.index()
    }

    /// Build the topology structure from a set of nodes and a set of connections.
    pub fn new_from_vec(nodes: Vec<N>, conns: Vec<C>, topo_type: TopologyType) -> Self {
        let mut topo = Self::new(topo_type);
        nodes.into_iter().for_each(|n| {
            topo.add_node(n);
        });
        conns.into_iter().for_each(|l| {
            topo.add_link(l);
        });
        topo
    }

    /// Returns a printable name for the topology
    pub fn name(&self) -> String {
        self.topology_type.name()
    }

    /// Retrieve a node by its id
    ///
    /// Returns an immutable node reference. Use this method for
    /// querying the node.
    pub fn node(&self, node_id: NodeId) -> &N {
        if let Some(n) = self.topo.node_weight(node_index(node_id)) {
            n
        } else {
            panic!("Invalid node id {}", node_id)
        }
    }

    /// Retrieve a mutable node by its id
    ///
    /// Returns an mutable node reference. Use this method for
    /// changing the node (user defined state mainly).
    pub fn node_mut(&mut self, node_id: NodeId) -> &mut N {
        if let Some(n) = self.topo.node_weight_mut(node_index(node_id)) {
            n
        } else {
            panic!("Invalid node id {}", node_id)
        }
    }

    /// Retrieve a connection by its id
    ///
    /// Returns an immutable connection reference. Use this method for
    /// querying the connection.
    pub fn connection(&self, conn_id: ConnectionId) -> &C {
        if let Some(l) = self.topo.edge_weight(edge_index(conn_id)) {
            l
        } else {
            panic!("Invalid connection id {}", conn_id)
        }
    }

    /// Retrieve a connection by its id
    ///
    /// Returns an mutable connection reference. Use this method for
    /// changing the connection (user defined state mainly).
    pub fn connection_mut(&mut self, conn_id: ConnectionId) -> &mut C {
        if let Some(l) = self.topo.edge_weight_mut(edge_index(conn_id)) {
            l
        } else {
            panic!("Invalid connection id {}", conn_id)
        }
    }

    /// Accessor for topology nodes
    ///
    /// Returns an iterator over the nodes that allows the caller to
    /// iterate through all the nodes in the topology. The set of nodes
    /// can be customized by using the iterator
    /// [`filter`](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.filter)
    /// method.
    #[inline]
    pub fn nodes<'a>(&'a self) -> impl Iterator<Item = &N> + 'a {
        self.topo
            .node_indices()
            .map(move |n| self.topo.node_weight(n).unwrap())
    }

    ///
    /// Returns a mutable iterator over the nodes that allows the caller to
    /// iterate through all the nodes in the topology and modifiy their state.
    #[inline]
    pub fn nodes_mut<'a>(&'a mut self) -> NodeWeightsMut<N> {
        self.topo.node_weights_mut()
    }

    /// Accessor for topology node ids
    ///
    #[inline]
    pub fn node_ids<'a>(&'a self) -> impl Iterator<Item = NodeId> + 'a {
        self.topo.node_indices().map(|id| id.index())
    }

    /// Accessor for topology connections
    ///
    /// Returns an iterator over the connections that allows the caller
    /// to iterate through all the connections in the topology. The set
    /// of connections can be customized by using the iterator
    /// [`filter`](https://doc.rust-lang.org/std/iter/trait.Iterator.html#method.filter)
    /// method.
    #[inline]
    pub fn connections(&self) -> impl Iterator<Item = &C> {
        self.topo
            .edge_indices()
            .map(move |edge| self.topo.edge_weight(edge).unwrap())
    }

    /// Accessor for topology connections
    ///
    /// Returns a mutable iterator over the connections that allows the caller
    /// to iterate through all the connections in the topology and modify their state
    #[inline]
    pub fn connections_mut<'a>(&'a mut self) -> EdgeWeightsMut<C> {
        self.topo.edge_weights_mut()
    }

    /// Returns an iterator over the connections of the node
    /// identified by node_id
    ///
    #[inline]
    pub fn node_connections<'a>(&'a self, node_id: &'a NodeId) -> impl Iterator<Item = &C> + 'a {
        self.topo
            .edges(node_index(*node_id))
            .map(move |edge| self.topo.edge_weight(edge.id()).unwrap())
    }
}

impl<N, C> TopologyFailure for Topology<N, C>
where
    N: Vertex + ElementFailure,
    C: Edge + ElementFailure + Debug,
{
    type Node = N;
    type Conn = C;

    /// Fail a node at `tick` time
    ///
    /// Mutates the state of the node and all its connection to a failed
    /// state. It is a no-op if the node is already in a failed state.
    fn fail_node(&mut self, node_id: NodeId, tick: MetaCycle) {
        let node = self.node_mut(node_id);
        if !node.is_failed() {
            node.fail(tick);
            // and fail all its connections
            let conns = self
                .node_connections(&node_id)
                .map(|c| c.id())
                .collect::<Vec<_>>();
            conns.iter().for_each(|c| {
                println!(
                    "Failing connection {}: {:?}",
                    c,
                    self.topo.edge_weight(edge_index(*c))
                );
                self.topo
                    .edge_weight_mut(edge_index(*c))
                    .unwrap()
                    .fail(tick);
            });
        }
    }

    /// Heal a node at `tick` time
    ///
    /// Mutates the state of the node and all its connection to another
    /// live node to a healed state. It is a no-op if the node is
    /// already in a healed state.
    fn heal_node(&mut self, node_id: NodeId, tick: MetaCycle) {
        let node = self.node_mut(node_id);
        if node.is_failed() {
            node.heal(tick);

            let mut healed_neighbors = Vec::new();
            healed_neighbors.push(node_id); // push myself to make the test easy
            for conn in self.node_connections(&node_id) {
                let pair = if conn.source() == node_id {
                    conn.sink()
                } else {
                    conn.source()
                };
                if !self.node(pair).is_failed() {
                    healed_neighbors.push(pair);
                }
            }
            // and heal all its connections for which the neighbor is live
            for conn in self.connections_mut().filter(|c| {
                healed_neighbors.contains(&c.source()) && healed_neighbors.contains(&c.sink())
            }) {
                conn.heal(tick);
            }
        }
    }

    /// Fail a connection
    ///
    /// Mutates the state of a connection to failed. It also checks
    /// whether all the connections into the nodes at the ends of the
    /// connection are alive, and if none of them is, then set the node
    /// as failed.
    /// It is a no-op if the connection was already in a failed state.
    fn fail_connection(&mut self, conn_id: ConnectionId, tick: MetaCycle) {
        if !self.connection(conn_id).is_failed() {
            let conn = self.connection(conn_id);
            let (left_id, right_id) = (conn.source(), conn.sink());
            self.connection_mut(conn_id).fail(tick);
            // check whether we need to fail the nodes
            for n in [left_id, right_id].iter() {
                let live_cons = self.node_connections(n).filter(|c| !c.is_failed()).count();
                if live_cons == 0 {
                    self.fail_node(*n, tick);
                }
            }
        }
    }

    /// Heal a connection
    ///
    /// Mutates the state of a connection to healed.  For symmetry, it
    /// might be appealing to also set the state of its nodes to
    /// healed. However, we are assuming that healing a node might
    /// require more than just a healed connection, so we leave healing
    /// the node to the higher level logic.
    ///
    /// It is a no-op if the connection was already in a healed state.
    fn heal_connection(&mut self, conn_id: ConnectionId, tick: MetaCycle) {
        self.connection_mut(conn_id).heal(tick);
    }
}

/// This simply redirects to the actual topology implementation
impl<N, C> Layout2D for Topology<N, C>
where
    N: Vertex,
    C: Edge + Debug,
{
    /// The X extent in a virtual canvas
    fn get_max_x(&self) -> usize {
        match &self.topology_type {
            TopologyType::Mesh(m) => m.get_max_x(),
            TopologyType::Torus(t) => t.get_max_x(),
            // by default pack the number of nodes into a rectangle
            _ => (self.topo.node_count() as f64).sqrt().ceil() as usize,
        }
    }
    /// The Y extent in a virtual canvas
    fn get_max_y(&self) -> usize {
        match &self.topology_type {
            TopologyType::Mesh(m) => m.get_max_y(),
            TopologyType::Torus(t) => t.get_max_y(),
            // by default pack the number of nodes into the smallest rectangle
            _ => (self.topo.node_count() - 1) / self.get_max_x() + 1,
        }
    }
    /// Node coordinates in a the virtual canvas
    fn get_node_coordinates(&self, node_id: NodeId) -> Coordinates {
        match &self.topology_type {
            TopologyType::Mesh(m) => m.get_node_coordinates(node_id),
            TopologyType::Torus(t) => t.get_node_coordinates(node_id),
            _ => {
                let x = node_id % self.get_max_x();
                let y = node_id / self.get_max_x();
                Coordinates::new(x, y)
            }
        }
    }
}

impl<N, C> Debug for Topology<N, C>
where
    N: Vertex + Debug,
    C: Edge + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        writeln!(f, "Topology: {}", self.topology_type.name())?;
        writeln!(f, "Nodes:\n  {:?}", self.nodes().format("\n  "))?;
        writeln!(f, "Connections:\n  {:?}", self.connections().format("\n  "))
    }
}

/// Topologies are displayed by generating a dot format string.
///
/// Our topologies are di-graphs, edges representing connections that are
/// bidirectional.
impl<N, C> std::fmt::Display for Topology<N, C>
where
    N: Vertex,
    C: Edge + Ord + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        const INDENT: &str = "  ";
        writeln!(f, "graph \"{}\" {{", self.topology_type.name())?;
        for c in self.connections().sorted() {
            writeln!(
                f,
                "{} {} -- {} [label=\"{}\"]",
                INDENT,
                c.source(),
                c.sink(),
                c.id()
            )?;
        }
        writeln!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mktemp::Temp;
    use std::cmp::Ordering;
    use std::fs::File;
    use std::io::prelude::*;
    use std::process::Command;

    #[derive(Copy, Clone, Debug, PartialEq, Eq, Ord, PartialOrd)]
    enum FailureState {
        WORKING,
        FAILED,
    }

    #[derive(Debug, Eq)]
    pub struct Node {
        id: NodeId,
        state: (MetaCycle, FailureState),
    }
    impl Vertex for Node {
        fn new_vertex() -> Self {
            Node {
                id: 0,
                state: (0, FailureState::WORKING),
            }
        }
        fn id(&self) -> NodeId {
            self.id
        }
        fn set_id(&mut self, id: NodeId) {
            self.id = id;
        }
    }
    impl ElementFailure for Node {
        fn fail(&mut self, tick: MetaCycle) {
            println!("Failing node {} at {}", self.id(), tick);
            self.state = (tick, FailureState::FAILED);
        }
        fn heal(&mut self, tick: MetaCycle) {
            self.state = (tick, FailureState::WORKING);
        }
        fn is_failed(&self) -> bool {
            self.state.1 == FailureState::FAILED
        }
    }
    impl Ord for Node {
        fn cmp(&self, other: &Self) -> Ordering {
            self.id.cmp(&other.id)
        }
    }
    impl PartialOrd for Node {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl PartialEq for Node {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }

    #[derive(Debug, Eq)]
    pub struct Connection {
        id: ConnectionId,
        source: NodeId,
        sink: NodeId,
        state: (MetaCycle, FailureState),
    }
    impl Edge for Connection {
        fn new_edge(src_node: NodeId, dst_node: NodeId) -> Self {
            Connection {
                id: 0,
                source: src_node,
                sink: dst_node,
                state: (0, FailureState::WORKING),
            }
        }
        fn id(&self) -> ConnectionId {
            self.id
        }
        fn set_id(&mut self, id: ConnectionId) {
            self.id = id;
        }
        fn source(&self) -> NodeId {
            self.source
        }
        fn sink(&self) -> NodeId {
            self.sink
        }
    }
    impl ElementFailure for Connection {
        fn fail(&mut self, tick: MetaCycle) {
            println!("Failing connection {} at {}", self.id(), tick);
            self.state = (tick, FailureState::FAILED);
        }
        fn heal(&mut self, tick: MetaCycle) {
            self.state = (tick, FailureState::WORKING);
        }
        fn is_failed(&self) -> bool {
            self.state.1 == FailureState::FAILED
        }
    }
    impl Ord for Connection {
        fn cmp(&self, other: &Self) -> Ordering {
            self.id.cmp(&other.id)
        }
    }
    impl PartialOrd for Connection {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl PartialEq for Connection {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }

    pub fn count_connections(node_id: NodeId, topo: &Topology<Node, Connection>) -> usize {
        topo.node_connections(&node_id).count()
    }

    #[test]
    fn test_conn_ids() {
        let nodes: Vec<Node> = vec![Node::new_vertex(), Node::new_vertex(), Node::new_vertex()];
        let conn: Vec<Connection> = vec![
            Connection::new_edge(nodes[0].id(), nodes[1].id()),
            Connection::new_edge(nodes[1].id(), nodes[2].id()),
            Connection::new_edge(nodes[2].id(), nodes[0].id()),
        ];

        let topo: Topology<Node, Connection> =
            Topology::new_from_vec(nodes, conn, TopologyType::Handcrafted);
        assert_eq!(
            topo.connections().map(|c| c.id()).collect::<Vec<_>>(),
            vec![0, 1, 2]
        )
    }
    #[test]
    fn test_dot() {
        let topo: Topology<Node, Connection> = Hypercube::hypercube(4);
        let temp_dir = Temp::new_dir().unwrap();
        let mut temp_path = temp_dir.to_path_buf();
        temp_path.push("hyper4.dot");
        let dot_name = String::from(temp_path.as_path().as_os_str().to_str().unwrap());
        println!("Writing to {:?}", dot_name);
        let mut file: File = File::create(&temp_path).expect("failed creating hyper4.dot");
        writeln!(file, "{}", topo).expect("failed to write the topology");
        if let Ok(dot) = which::which("dot") {
            let mut pdf = dot_name.clone();
            pdf.replace_range(dot_name.len() - 4.., ".pdf");
            println!("Generating pdf: {}", pdf);
            let dot_cmd = vec!["-Tpdf", &dot_name, "-o", &pdf];
            let res = Command::new(&dot).args(&dot_cmd).output();
            assert!(res.is_ok());
            assert!(std::path::Path::new(&pdf).exists());
        }
        // display the dot format on the screen too.
        println!("Topology: {}", topo);
    }
}
