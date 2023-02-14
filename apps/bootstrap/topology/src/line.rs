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

/// Build a star with hosts end points + 1 hub
/// A line topology
///
/// An unrealistic topology that we can use to test latency.
/// The network diameter determines the latency of seeing changes across the network, and line
/// is easy to reason about.
#[derive(Debug, Serialize, Deserialize)]
pub struct Line {
    /// the number of nodes in the line
    nodes: usize,
}

impl Line {
    pub fn line<N, C>(num_nodes: usize) -> Topology<N, C>
    where
        N: Vertex,
        C: Edge + std::fmt::Debug,
    {
        let mut topo = Topology::new(TopologyType::Line(Self { nodes: num_nodes }));

        for n in 0..num_nodes {
            topo.add_node(N::new_vertex());
            if n > 0 {
                topo.add_link(C::new_edge(topo.node(n - 1).id(), topo.node(n).id()));
            }
        }
        topo
    }

    pub fn name(&self) -> String {
        format!("Line ({} nodes)", self.nodes)
    }
}

#[cfg(test)]
mod tests {
    use crate::line::Line;
    use crate::tests::{Connection, Node};
    use crate::Topology;

    #[test]
    fn test_line() {
        let nodes = 5;
        let topo: Topology<Node, Connection> = Line::line(5);
        println!("Topology: {:?}\n", topo);
        assert_eq!(topo.nodes().count(), nodes);
        assert_eq!(topo.connections().count(), nodes - 1);
    }
}
