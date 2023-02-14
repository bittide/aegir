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

//! system architectural specification
//!
//! A system represents a topology of nodes connected with links.
//! For bittide modeling there are currently three kinds of system architectures:
//!   - an application specification -- represents application level
//!   pipelines: sercice nodes and connections.
//!   - a hardware specification -- represents a bittide system of hardware
//!   compute and switch nodes and the physical links between them.
//!   - a virtual partition specification -- a "view" of a hardware
//!   specification (not yet implemented)

use crate::calendar::Buffering;
use itertools::structs::Unique;
use itertools::Itertools;
use link::NonFramingLinkTrait;
use petgraph::graph;
use petgraph::graph::{Edges, Neighbors};
use petgraph::prelude::*;
use std::cell::RefCell;
use std::fmt::{Display, Formatter};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::*;

/// Each graph in aegir has a unique ID. This helps distinguish multiple
/// applications graphs and HW topologies.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct GraphId {
    value: usize,
}

impl Display for GraphId {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.value)
    }
}

fn next_system_id() -> GraphId {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let next_value = COUNTER.fetch_add(1, Ordering::Relaxed);
    GraphId { value: next_value }
}

#[derive(Clone, Debug)]
pub struct SystemSpec<const B: Buffering, Node, Link>
where
    Node: NodeSpec<B> + Sized,
    Link: LinkSpec + Sized,
{
    // Nodes are stored through Rc<RefCell<>> in order to enable cross
    // system references. In particular, the main use case is to have a
    // application specification and a system specification. In order to
    // simulate the application on the system, we actually simulate the
    // system spec, after we set the application (set_app) with a reference
    // to an app node.
    //
    // Note: for now we use Rc, since the code is not parallelized and we
    // don't need to pay the price of synchronization. Switch to Arc when we
    // do that. Would be nice to have an automatic way to switch with a
    // "feature".
    //
    // TODO(cascaval): apply the same treatment to Link, so that we can
    // fully handle the simulation within system spec and avoid replicating
    // Links in sim.rs. However, since all that code is common, would be
    // good to find a way to implement the common code as part of the trait
    // (more Rust doc reading!).
    /// system topology
    pub(crate) topo: Graph<Rc<RefCell<Node>>, Link>,
    id: GraphId,
}

impl<const BUFFERING: Buffering, NS, LS> SystemSpec<BUFFERING, NS, LS>
where
    NS: NodeSpec<BUFFERING> + StatefulNode + Sized + std::fmt::Debug,
    LS: LinkSpec + Sized + std::fmt::Debug,
{
    pub fn set_node_state(&self, node_id: NodeIndex, state: Data) {
        self.get_node(node_id)
            .borrow_mut()
            .set_persistent_state(state);
    }
}

impl<const BUFFERING: Buffering, NS, LS> SystemSpec<BUFFERING, NS, LS>
where
    NS: NodeSpec<BUFFERING> + Sized + std::fmt::Debug,
    LS: LinkSpec + NonFramingLinkTrait + Sized + std::fmt::Debug,
{
    pub fn link_simplex(&mut self, src: NodeIndex, dst: NodeIndex, link: LS) -> EdgeIndex {
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
        self.topo.add_edge(src, dst, link)
    }
}

impl<const BUFFERING: Buffering, NS, LS> SystemSpec<BUFFERING, NS, LS>
where
    NS: NodeSpec<BUFFERING> + std::fmt::Debug,
    LS: LinkSpec + std::fmt::Debug,
{
    pub fn compute_nodes(&self) -> Vec<NodeIndex> {
        self.iter_nodes()
            .filter(|node_id| {
                self.get_node(*node_id)
                    .borrow()
                    .into_provisioned_switch_node()
                    .is_none()
            })
            .collect::<Vec<_>>()
    }

    pub fn switch_nodes(&self) -> Vec<NodeIndex> {
        self.iter_nodes()
            .filter(|node_id| {
                self.get_node(*node_id)
                    .borrow()
                    .into_provisioned_switch_node()
                    .is_some()
            })
            .collect::<Vec<_>>()
    }
}

impl<const BUFFERING: Buffering, NS, LS> SystemSpec<BUFFERING, NS, LS>
where
    NS: NodeSpec<BUFFERING> + Sized + std::fmt::Debug,
    LS: LinkSpec + Sized + std::fmt::Debug,
{
    pub fn new() -> Self {
        Self {
            topo: Graph::<Rc<RefCell<NS>>, LS>::new(),
            id: next_system_id(),
        }
    }

    pub fn id(&self) -> GraphId {
        self.id.clone()
    }

    pub fn add_node(&mut self, node: NS) -> NodeIndex {
        self.topo.add_node(Rc::new(RefCell::new(node)))
    }

    pub fn is_empty(&self) -> bool {
        self.topo.node_count() == 0
    }

    /// return a reference to the node.
    pub fn get_node(&self, node_id: NodeIndex) -> Rc<RefCell<NS>> {
        assert!(node_id.index() < self.topo.node_count());
        Rc::clone(self.topo.node_weight(node_id).unwrap())
    }

    /// Returns the first node index matching name.
    pub fn get_node_index_by_name(&self, name: &str) -> Option<NodeIndex> {
        return self
            .topo
            .node_indices()
            .find(|n| self.get_node(*n).borrow().name() == name);
    }

    /// returns the first node matching name
    pub fn get_node_by_name(&self, name: &str) -> Rc<RefCell<NS>> {
        if let Some(node) = self.get_node_index_by_name(name) {
            self.get_node(node)
        } else {
            panic!("No such node {}", name)
        }
    }

    /// returns the number of inputs and outputs of the node
    pub fn get_node_inout_count(&self, node_id: NodeIndex) -> (usize, usize) {
        (
            self.topo
                .edges_directed(node_id, Direction::Incoming)
                .count(),
            self.topo
                .edges_directed(node_id, Direction::Outgoing)
                .count(),
        )
    }

    /// returns an interator over all nodes in the topology (their indices)
    pub fn iter_nodes(&self) -> graph::NodeIndices {
        self.topo.node_indices()
    }

    /// return a reference to the link.
    pub fn get_link(&self, link_id: EdgeIndex) -> &dyn LinkSpec {
        assert!(link_id.index() < self.topo.edge_count());
        self.topo.edge_weight(link_id).unwrap()
    }

    pub fn ugn(&self, link_id: EdgeIndex) -> i64 {
        let (src, dst) = self.get_link_endpoints(link_id);
        let src_cycles = self
            .get_node(src)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles() as i64;
        let dst_cycles = self
            .get_node(dst)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles() as i64;
        let link_latency = self.get_link(link_id).latency().0 as i64;
        dst_cycles - src_cycles + link_latency
    }

    pub fn get_link_mut(&mut self, link_id: EdgeIndex) -> &mut dyn LinkSpec {
        assert!(link_id.index() < self.topo.edge_count());
        self.topo.edge_weight_mut(link_id).unwrap()
    }

    /// return an interator over the node's input links
    ///
    /// Note that there is no guarantee that the iterator returns the links
    /// in the order of their dst_ports. While it may be that we can
    /// implement such an ordering, by implementing Ord for LinkSpec, at
    /// this time, the order is random.
    pub fn get_input_links(&self, node_id: NodeIndex) -> Edges<LS, petgraph::Directed> {
        self.topo.edges_directed(node_id, Direction::Incoming)
    }

    /// return an interator over the node's output links
    ///
    /// Note that there is no guarantee that the iterator returns the links
    /// in the order of their src_ports. While it may be that we can
    /// implement such an ordering, by implementing Ord for LinkSpec, at
    /// this time, the order is random.
    pub fn get_output_links(&self, node_id: NodeIndex) -> Edges<LS, petgraph::Directed> {
        self.topo.edges_directed(node_id, Direction::Outgoing)
    }

    /// returns an iterator over all links in the topology (their indices)
    pub fn iter_links(&self) -> graph::EdgeIndices {
        self.topo.edge_indices()
    }

    /// return an iterator over the set of neighbors
    ///
    /// note that petgraph returns the a node as a neighbor multiple times,
    /// once for every edge connecting the two nodes; therefore, we filter
    /// them using itertools::Itertools::unique().
    pub fn neighbors(&self, node_id: NodeIndex) -> Unique<Neighbors<LS>> {
        self.topo.neighbors_undirected(node_id).unique()
    }

    pub fn get_link_endpoints(&self, link: EdgeIndex) -> (NodeIndex, NodeIndex) {
        if let Some((src, dst)) = self.topo.edge_endpoints(link) {
            (src, dst)
        } else {
            panic!("missing destination node for edge {}", link.index());
        }
    }

    /* TODO(cascaval): remove
    // bidirectional link between nodes; this is shorthand for a symmetric pair of simplex links;
    // one of the sides must be declared the framing lead, with the other then the framing follower
    // to resolve frame timing when frequencies do not match (pls see documentation for
    // link_simplex)
    #[allow(clippy::too_many_arguments)]
    pub fn link_duplex(
        &mut self,
        lead_node: &NodeHandle,
        lead_out_port: Port,
        lead_in_port: Port,
        follower_node: &NodeHandle,
        follower_out_port: Port,
        follower_in_port: Port,
        l_f_frame_size: usize,
        f_l_frame_size: usize,
        latency: Latency,
    ) {
        // TODO(samanzano): Explain why
        // in a duplex link the framing leads
        // are criss-crossed
        self.link_simplex(
            lead_node,
            lead_out_port,
            follower_node,
            follower_in_port,
            FramingLead::Src,
            l_f_frame_size,
            latency,
        );
        self.link_simplex(
            follower_node,
            follower_out_port,
            lead_node,
            lead_in_port,
            FramingLead::Dst,
            f_l_frame_size,
            latency,
        );
    }
    */

    /*
    // would be nice to have this this functionality here and get rid of SystemSimulation.
    // but I couldn't convince the borrow checker to let me get the input/output frames
    // as mutable.
    // Tried:
    //  - directly work on the topology and store state in the Links (LinkSpec::get_state)
    //  - splitting the link state into SystemSimulation and accessing the state through it.
    //
    // The combinatoon of map closures or even iterations with borrowing self as mutable
    // in every iteration is a killer.
    //
    // need to move links to an Rc<RefCell<LinkSpec>> in order to have
    // interior mutability.

    pub fn simulate(&mut self, cycles: Cycle) -> Result<(), Error> {
        // the graph is "frozen": normalize the frequencies
        self.normalize_frequencies();

        for _ in 0..cycles {
            self.simulate_one_cycle()?;
            // TODO: inspec the state if needed
        }
        Ok(())
    }

    /// step the system for one local cycle (as defined by its frequency)
    pub fn simulate_one_cycle(&mut self, sim_state: &mut SystemSimulation) -> Result<(), Error> {
        self.visitor.reset(&self.topo);
        while let Some(node_id) = self.visitor.next() {
            log::debug!("simulate_node {}", node_id.index());
            let mut node = self.get_node_mut(node_id);
            let mut outputs = sim_state.get_output_frames(node_id, &self);
            /*
            self
            .get_output_links(node_id)
            .map(|o| sim_state.get_next_src_frames(o.id(), &self))
            .flatten()
            .collect::<Vec<OutputFrameRef>>();
            */
            let inputs = self
                .get_input_links(node_id)
                .flat_map(|link| {
                    if let Some((src_idx, dst_idx)) = self.topo.edge_endpoints(link.id()) {
                        assert_eq!(node_id, dst_idx);
                        assert_ne!(src_idx, node_id);
                        // let mut termination = sim_state.get_termination_mut(link);
                        sim_state
                            .get_next_dst_frames(link.id(), &self)
                            .iter()
                            .map(|frame| if frame.valid { Some(&frame.data) } else { None })
                            .collect::<Vec<InputFrameRef>>()
                    } else {
                        vec![None]
                    }
                })
                .collect::<Vec<InputFrameRef>>();
            node.step(&inputs, &mut outputs)?;
        }
        Ok(())
    }
    */
    pub fn to_graphviz(&self) -> String {
        use petgraph::dot::{Config, Dot};

        let generator = Dot::with_attr_getters(
            &self.topo,
            &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &|_, edge| {
                format!(
                    "label=\"Link {}\nfs = {}\n{:?}\"; headlabel=\"{}\"; taillabel=\"{}\"",
                    edge.id().index(),
                    edge.weight().frame_size(),
                    edge.weight().latency(),
                    edge.weight().dst_port(),
                    edge.weight().src_port()
                )
            },
            &|_, node| {
                format!(
                    "label=\"{}\n(id: {})\"",
                    node.1.borrow().name(),
                    node.0.index()
                )
            },
        );
        format!("{:?}", generator)
    }

    // TODO(tammo): Implement external IO.
    //
    // declare a system-level input to fascilitate communication with the "outside world";  this is
    // a node input that is not satisfied within the system (via connection with intra-system
    // nodes); this input can be bound (and unbound, and rebound) after the system is allocated
    // for, booted, and running
    // pub fn external_input(&mut self, _node: &NodeHandle, _width: usize) {
    //     unimplemented!()
    // }
    // declare a system-level output to fascilitate communication with the "outside world";  this is
    // a node output that is not satisfied within the system (via connection with intra-system
    // nodes); this output can be bound (and unbound, and rebound) after the system is allocated
    // for, booted, and running
    // pub fn external_output(&mut self, _node: &NodeHandle, _width: usize) {
    //     unimplemented!()
    // }

    // TODO: once we have simulation of hardware, these specifications will need to include bounds
    // on compute resources (both cycles and memory), and once we have that it will makes sense to
    // also allow specification of performance constraints (timing bounds); this will only be
    // meaningful once we start implementing resource allocation (which requires simulation of
    // isolation control mechanisms, calendars etc);  performance constraints would most obviously
    // apply be between external inputs and outputs, but possibly there is reason to support
    // internal constrains as well
}

impl<const BUFFERING: Buffering, NS, LS> Default for SystemSpec<BUFFERING, NS, LS>
where
    NS: NodeSpec<BUFFERING> + std::fmt::Debug,
    LS: LinkSpec + std::fmt::Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const BUFFERING: Buffering, NS, LS> std::fmt::Display for SystemSpec<BUFFERING, NS, LS>
where
    NS: NodeSpec<BUFFERING> + std::fmt::Debug,
    LS: LinkSpec + std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.to_graphviz())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Application, Connection, Service};
    fn no_action(
        _s: LoopbackRef,
        _i: &[InputFrameRef],
        _o: &mut [OutputFrameRef],
        _sc: &dyn SystemContext,
    ) {
    }

    #[test]
    fn test_graphviz() {
        let mut app_spec = Application::new();
        let n1 = Service::new("n1", no_action, None, FrequencyFactor(1));
        let n2 = Service::new("n2", no_action, None, FrequencyFactor(1));
        let s1 = app_spec.add_node(n1);
        let s2 = app_spec.add_node(n2);
        let link_spec = Connection::new_for_testing(0, 0, 8);
        let _l = app_spec.link_simplex_framing(s1, s2, link_spec.clone(), FramingLead::Src);
        let _l = app_spec.link_simplex_framing(s2, s1, link_spec.clone(), FramingLead::Dst);

        println!("{}", app_spec.to_graphviz());
        assert_eq!(
            app_spec.to_graphviz(),
            "digraph {\n    0 [ label=\"n1\n(id: 0)\"]\n    1 [ label=\"n2\n(id: 1)\"]\n    0 -> 1 [ label=\"Link 0\nfs = 8\nLatency(0)\"; headlabel=\"0\"; taillabel=\"0\"]\n    1 -> 0 [ label=\"Link 1\nfs = 8\nLatency(0)\"; headlabel=\"0\"; taillabel=\"0\"]\n}\n",
        );
    }
}
