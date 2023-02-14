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

use crate::layout::{Coordinates, Layout2D};
use crate::NodeId;
use crate::Topology;
use crate::TopologyType;
use crate::{Edge, Vertex};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

/// A torus topology
///
/// Each node is connected to its neighbors in each axis dimension.
#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct Torus {
    dims: Vec<usize>,
}

impl Torus {
    /// A torus builder
    pub fn torus<N, C>(dims: &[usize]) -> Topology<N, C>
    where
        N: Vertex,
        C: Edge + std::fmt::Debug,
    {
        let torus = Self {
            dims: dims.to_vec(),
        };
        let mut topo = Topology::new(TopologyType::Torus(torus.clone()));

        for _ in 0..torus.dims.iter().product() {
            topo.add_node(N::new_vertex());
        }

        // build the links: for each node, add the connections to their
        // "higher" node pairs.
        for e in torus.dims.iter().map(|&d| 0..d).multi_cartesian_product() {
            // e is a vector that contains the coordinates of a node
            for (d, m) in torus.dims.iter().enumerate() {
                let mut n = e.clone();
                n[d] = (e[d] + 1) % m;
                topo.add_link(C::new_edge(
                    topo.node(torus.linearize_index(&e)).id(),
                    topo.node(torus.linearize_index(&n)).id(),
                ));
            }
        }
        topo
    }

    pub fn name(&self) -> String {
        format!(
            "Torus {}D ({})",
            self.dims.len(),
            self.dims.iter().format("x")
        )
    }

    /// return the linear index of the element
    /// The element is represented as a vector of coordinates.
    fn linearize_index(&self, elem: &[usize]) -> usize {
        let mut index: usize = 0;
        for (d, c) in elem.iter().enumerate() {
            index += c * self.dims[0..d].iter().product::<usize>();
        }
        index
    }
}

// Implemented only for a 2D torus for now
impl Layout2D for Torus {
    /// The X extent in a virtual canvas
    fn get_max_x(&self) -> usize {
        if self.dims.len() > 3 {
            let num_nodes: usize = self.dims.iter().product();
            return (num_nodes as f64).sqrt().ceil() as usize;
        }
        let mut x = self.dims[0];
        for i in 2..self.dims.len() {
            x *= (self.dims[i] as f64).sqrt().ceil() as usize;
        }
        return x;
    }
    /// The Y extent in a virtual canvas
    fn get_max_y(&self) -> usize {
        if self.dims.len() > 3 {
            let num_nodes: usize = self.dims.iter().product();
            return (num_nodes - 1) / self.get_max_x() + 1;
        }
        let mut y = self.dims[1];
        for i in 2..self.dims.len() {
            y *= (self.dims[i] as f64).sqrt().ceil() as usize;
        }
        return y;
    }
    /// Node coordinates in a the virtual canvas
    fn get_node_coordinates(&self, node_id: NodeId) -> Coordinates {
        if self.dims.len() > 3 {
            // default layout: we just draw a rectangle: ceil(sqrt(n)) * ceil(sqrt(n))
            let x = node_id % self.get_max_x();
            let y = node_id / self.get_max_x();
            return Coordinates::new(x, y);
        }
        // otherwise
        let plane_nodes = self.dims[0..2].iter().product::<usize>();
        let plane = node_id / plane_nodes;
        let plane_x = ((plane as f64).sqrt().ceil() as usize * self.dims[0]) % self.get_max_x();
        let plane_y = ((plane as f64).sqrt().ceil() as usize * self.dims[0]) / self.get_max_x()
            * self.dims[1];
        let x = node_id % self.dims[0] + plane_x;
        let y = (node_id / self.dims[0]) % self.dims[1] + plane_y;
        // Potential layout for higher dimensions tori!
        //
        // For higher dimensional tori, my current thinking is that we can
        // peel one dimension at a time and fold the nodes in the n
        // dimension into the n-1 dimensions similarly -- so plane is
        // actually representing the n-1 dimensional space, and we fold the
        // n dimension ... equally distributed along all the other n-1 dims??
        // I'd expect people have studied this, need to find some references!
        //
        // println!(
        //     "get_node_coordinates: node_id = {}, plane = {}, plane_x = {}, plane_y = {}",
        //     node_id, plane, plane_x, plane_y
        // );
        Coordinates::new(x, y)
    }
}

#[cfg(test)]
mod tests {
    use crate::layout::{Coordinates, Layout2D};
    use crate::tests::{count_connections, Connection, Node};
    use crate::torus::Torus;
    use crate::Topology;
    use crate::{Edge, Vertex};
    use itertools::Itertools;

    #[test]
    fn test_torus() {
        let (x, y, z) = (3, 4, 3);
        let topo: Topology<Node, Connection> = Torus::torus(&[x, y, z]);
        println!("Topology: {:?}", topo);
        assert_eq!(topo.nodes().count(), x * y * z);
        assert_eq!(topo.connections().count(), x * y * z * 3); // each node has 6 links

        for n in topo.nodes() {
            assert_eq!(count_connections(n.id(), &topo), 6);
        }
        let node_id = 1 + 3 + 12; // node (1,1,1)
        let n = topo.node(node_id);

        /*
          1  2  3    13 14 15    25 26 27
          4  5  6    16 *17 18   28 29 30
          7  8  9    19 20 21    31 32 33
         10 11 12    22 23 24    34 35 36

         17 is connected to 16, 18, 14, 20, 5, 29
        */
        println!("Node: {:?}", n);
        println!(
            "Connections:\n  {:?}",
            topo.node_connections(&n.id()).format("\n  ")
        );
        let conn_set = vec![
            topo.node(node_id - 1).id(),
            topo.node(node_id + 1).id(),
            topo.node(node_id - x).id(),
            topo.node(node_id + x).id(),
            topo.node(node_id - x * y).id(),
            topo.node(node_id + x * y).id(),
        ];
        for c in topo.node_connections(&n.id()) {
            assert!(
                (c.source() == n.id() && conn_set.contains(&c.sink()))
                    || (c.sink() == n.id() && conn_set.contains(&c.source()))
            );
        }
    }

    #[test]
    fn test_torus2d_layout() {
        let (x, y) = (5, 3);
        let topo: Topology<Node, Connection> = Torus::torus(&[x, y]);
        assert_eq!(topo.get_max_x(), x, "Invalid x-extent");
        assert_eq!(topo.get_max_y(), y, "Invalid y-extent");
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
            topo.get_node_coordinates(topo.node(13).id()),
            Coordinates::new(3, 2),
            "Invalid node 14 coordinates"
        );
    }

    #[test]
    fn test_torus3d_layout() {
        let (x, y, z) = (3, 4, 3);
        let topo: Topology<Node, Connection> = Torus::torus(&[x, y, z]);
        assert_eq!(topo.get_max_x(), 3 * 2, "Invalid x-extent");
        assert_eq!(topo.get_max_y(), 4 * 2, "Invalid y-extent");
        assert_eq!(
            topo.get_node_coordinates(topo.node(0).id()),
            Coordinates::new(0, 0),
            "Invalid node 1 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(3).id()),
            Coordinates::new(0, 1),
            "Invalid node 4 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(11).id()),
            Coordinates::new(2, 3),
            "Invalid node 12 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(12).id()),
            Coordinates::new(3, 0),
            "Invalid node 13 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(24).id()),
            Coordinates::new(0, 4),
            "Invalid node 25 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(35).id()),
            Coordinates::new(2, 7),
            "Invalid node 36 coordinates"
        );
    }
}
