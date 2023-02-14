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

/// The star topology builder
///
/// Build a star with hosts end points + 1 hub
#[derive(Debug, Serialize, Deserialize)]
pub struct Star {
    /// number of hosts
    hosts: usize,
}

impl Star {
    /// generate a Star topology of hosts edge nodes + 1 hub node
    pub fn star<N: Vertex, C: Edge + std::fmt::Debug>(hosts: usize) -> Topology<N, C> {
        let mut topo = Topology::new(TopologyType::Star(Self { hosts }));

        for _ in 0..(hosts + 1) {
            // hub + hosts
            topo.add_node(N::new_vertex());
        }

        for y in 1..(hosts + 1) {
            topo.add_link(C::new_edge(topo.node(0).id(), topo.node(y).id()));
        }
        topo
    }

    pub fn name(&self) -> String {
        format!("Star ({} hosts + 1 hub)", self.hosts)
    }
}

#[cfg(test)]
mod tests {
    use crate::layout::{Coordinates, Layout2D};
    use crate::star::Star;
    use crate::tests::{count_connections, Connection, Node};
    use crate::Topology;
    use crate::Vertex;
    // use itertools::Itertools;

    #[test]
    fn test_star() {
        let hosts = 5;
        let topo: Topology<Node, Connection> = Star::star(hosts);
        println!("Topology: {:?}", topo);
        assert_eq!(topo.nodes().count(), hosts + 1);
        assert_eq!(topo.connections().count(), hosts); // one connection per host

        let hub = topo.node(0); // the hub should have a connection to every host
        assert_eq!(count_connections(hub.id(), &topo), hosts);
        for i in 1..(hosts + 1) {
            // everyone else has one connection
            assert_eq!(count_connections(topo.node(i).id(), &topo), 1);
        }

        assert_eq!(topo.get_max_x(), 3);
        assert_eq!(topo.get_max_y(), 2);
    }

    #[test]
    fn test_star_layout() {
        let hosts = 17;
        let topo: Topology<Node, Connection> = Star::star(hosts);
        assert_eq!(topo.get_max_x(), 5, "Invalid x-extent");
        assert_eq!(topo.get_max_y(), 4, "Invalid y-extent");
        assert_eq!(
            topo.get_node_coordinates(topo.node(0).id()),
            Coordinates::new(0, 0),
            "Invalid node 1 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(5).id()),
            Coordinates::new(0, 1),
            "Invalid node 6 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(17).id()),
            Coordinates::new(2, 3),
            "Invalid node 18 coordinates"
        );
    }
}
