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

//! # Failures
//!
//! Dealing with failures requires ensuring that all the simulator
//! components can handle the cases when a component has failed. We have
//! different options:
//!
//! 1. keep the Vertex or Edge in the topology and have its state be
//! "failure". This way, the component is still visited, but there is no
//! reaction (or status reporting) to any of the events.
//!
//! 2. Remove the Vertex or the Edge from the topology (at least
//! temporarily) and not visit it anymore. However, the simulator may
//! have references (ids) to the previous components, so it may still
//! ask for the component directly, in which case, it has to deal with
//! an optional result.
//!
//! Given these two choices, it is preferable to put the Vertex/Edge
//! in a failed state: and thus we provide two methods, fail_node and
//! fail_connection that transition the state for the component. A node
//! for which all the connections are failed, should also be considered
//! failed.

use crate::{ConnectionId, NodeId};
use crate::{Edge, Vertex};

/// Define a global clock -- we need this for tagging fail and heal
/// events.
pub type MetaCycle = u64;

/// Interface for failure handling of topology elements.
///
/// To deal with failures, topology elements, nodes and connections, need to
/// encapsulate state that records healing and failure events at moments in
/// time. The failure state can also be queried.
pub trait ElementFailure {
    /// Set an element as failed starting at `tick`.
    fn fail(&mut self, tick: MetaCycle);
    /// Set an element as healed (not failed) starting at `tick`.
    fn heal(&mut self, tick: MetaCycle);
    /// Query the failure state of the element.
    fn is_failed(&self) -> bool;
}

/// Interface for topology to manage failures
///
pub trait TopologyFailure {
    type Node: Vertex + ElementFailure;
    type Conn: Edge + ElementFailure;

    /// Fail a node at `tick` time
    ///
    /// Mutates the state of the node and all its connection to a failed
    /// state. It is a no-op if the node is already in a failed state.
    fn fail_node(&mut self, node_id: NodeId, tick: MetaCycle);

    /// Heal a node at `tick` time
    ///
    /// Mutates the state of the node and all its connection to another
    /// live node to a healed state. It is a no-op if the node is
    /// already in a healed state.
    fn heal_node(&mut self, node_id: NodeId, tick: MetaCycle);

    /// Fail a connection
    ///
    /// Mutates the state of a connection to failed. It also checks
    /// whether all the connections into the nodes at the ends of the
    /// connection are alive, and if none of them is, then set the node
    /// as failed.
    /// It is a no-op if the connection was already in a failed state.
    fn fail_connection(&mut self, conn_id: ConnectionId, tick: MetaCycle);

    /// Heal a connection
    ///
    /// Mutates the state of a connection to healed.  For symmetry, it
    /// might be appealing to also set the state of its nodes to
    /// healed. However, we are assuming that healing a node might
    /// require more than just a healed connection, so we leave healing
    /// the node to the higher level logic.
    ///
    /// It is a no-op if the connection was already in a healed state.
    fn heal_connection(&mut self, conn_id: ConnectionId, tick: MetaCycle);
}

#[cfg(test)]
mod tests {
    use crate::failure::{ElementFailure, MetaCycle};
    use crate::tests::{Connection, Node};
    use crate::{Edge, Vertex};
    use crate::{Mesh, Topology, TopologyFailure};

    #[test]
    fn test_failures() {
        // build a 4x3 mesh
        let mut topo: Topology<Node, Connection> = Mesh::mesh(&[4, 3]);
        println!("Topology: {:?}\n", topo);

        let n11id = 1;
        // kill node at (1,0) and check that its connections are failed,
        // looking from its neighbors
        println!("Attempting to fail node: {}", n11id);
        let mut tick: MetaCycle = 19;
        topo.fail_node(n11id, tick);
        println!("Failed node: {:?}", topo.node(n11id));
        for idx in [0, 2, 5].iter() {
            for conn in topo
                .node_connections(&topo.node(*idx).id())
                .filter(|c| c.source() == n11id || c.sink() == n11id)
            {
                println!("Connection: {:?}", conn);
                assert!(conn.is_failed());
            }
        }

        // and now heal the node
        tick += 6;
        topo.heal_node(n11id, tick);
        println!("Healed node: {:?}", topo.node(n11id));
        for idx in [0, 2, 5].iter() {
            for conn in topo
                .node_connections(&topo.node(*idx).id())
                .filter(|c| c.source() == n11id || c.sink() == n11id)
            {
                println!("Connection: {:?}", conn);
                assert!(!conn.is_failed());
            }
        }
    }
}
