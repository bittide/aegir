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

use crate::Topology;
use crate::TopologyType;
use crate::{Edge, Vertex};
use serde::{Deserialize, Serialize};

/// A fully connected topology of `nodes` size.
///
/// It represents a topology in which each node is connected to every
/// other node.
///
/// To build a triangle topology (e.g., for the FPGA emulation) create a
/// fully connected topology with 3 nodes.
#[derive(Debug, Serialize, Deserialize)]
pub struct FullyConnected {
    nodes: usize,
}

impl FullyConnected {
    /// The fully connected topology builder.
    pub fn full<N, C>(num_nodes: usize) -> Topology<N, C>
    where
        N: Vertex,
        C: Edge + std::fmt::Debug,
    {
        let mut topo = Topology::new(TopologyType::Full(Self { nodes: num_nodes }));
        for n in 0..num_nodes {
            topo.add_node(N::new_vertex());
            for n1 in 0..n {
                topo.add_link(C::new_edge(topo.node(n1).id(), topo.node(n).id()));
            }
        }
        topo
    }

    pub fn name(&self) -> String {
        format!("FullyConnected ({} nodes)", self.nodes)
    }
}

#[cfg(test)]
mod tests {
    // use crate::layout::Layout2D;
    use crate::full::FullyConnected;
    use crate::tests::{Connection, Node};
    use crate::Topology;

    #[test]
    fn test_fully_connected() {
        let nodes = 4;
        let topo: Topology<Node, Connection> = FullyConnected::full(nodes);
        println!("Topology: {:?}\n", topo);
        assert_eq!(topo.nodes().count(), nodes);
        assert_eq!(
            topo.connections().count(),
            nodes * (nodes - 1) / 2 // each node has n-1 links
        );
    }
}
