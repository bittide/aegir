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

/// A hypercube topology
///
/// Building a hypecube will result in a topology with 2^degree nodes.
#[derive(Debug, Serialize, Deserialize)]
pub struct Hypercube {
    degree: usize,
    nodes: usize,
}

impl Hypercube {
    /// They hypercube topology builder.
    pub fn hypercube<N, C>(degree: usize) -> Topology<N, C>
    where
        N: Vertex,
        C: Edge + std::fmt::Debug,
    {
        let num_nodes = 2_usize.pow(degree as u32);
        let mut topo = Topology::new(TopologyType::Hypercube(Self {
            degree,
            nodes: num_nodes,
        }));

        for _ in 0..num_nodes {
            topo.add_node(N::new_vertex());
        }

        // build the links: for each node, add the connections to their
        // "higher" node pairs, that is connect the bit 0s to the bit 1s
        for n in 0..num_nodes {
            for b in 0..degree {
                if (n & (1 << b)) == 0 {
                    log::debug!(
                        "Linking node {:0width$b} with {:0width$b}",
                        n,
                        (n | (1 << b)),
                        width = degree
                    );
                    topo.add_link(C::new_edge(topo.node(n).id(), topo.node(n | (1 << b)).id()));
                }
            }
        }
        topo
    }
    pub fn name(&self) -> String {
        format!("Hypercube ({} degree)", self.degree)
    }
}

#[cfg(test)]
mod tests {
    // use crate::layout::Layout2D;
    use crate::hypercube::Hypercube;
    use crate::tests::{count_connections, Connection, Node};
    use crate::Topology;
    use crate::Vertex;

    #[test]
    fn test_hypercube() {
        let degree = 4;
        let topo: Topology<Node, Connection> = Hypercube::hypercube(degree);
        println!("Topology: {:?}", topo);
        assert_eq!(topo.nodes().count(), 2_usize.pow(degree as u32));
        assert_eq!(
            topo.connections().count(),
            2_usize.pow(degree as u32) * degree / 2 // each node has degree links
        );

        for n in topo.nodes() {
            assert_eq!(count_connections(n.id(), &topo), degree);
        }
    }
}
