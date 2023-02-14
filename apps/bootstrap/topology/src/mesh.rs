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

/// return the linear index of the element
/// The element is represented as a vector of coordinates.
fn linearize_index(dims: &[usize], elem: &[usize]) -> usize {
    let mut index: usize = 0;
    for (d, c) in elem.iter().enumerate() {
        index += c * dims[0..d].iter().product::<usize>();
    }
    index
}

/// A multidimensional mesh topology
#[derive(Serialize, Deserialize, Debug)]
pub struct Mesh {
    /// the extents in each dimension
    dims: Vec<usize>,
}

impl Mesh {
    /// A <dim>-D grid topology
    ///
    /// For example a 2D mesh looks like this:
    /// <pre>
    /// x --- x --- x --- x   ^
    /// |     |     |     |   |
    /// x --- x --- x --- x   y-dim
    /// |     |     |     |   |
    /// x --- x --- x --- x   v
    /// < ----- x-dim ---->
    /// </pre>
    pub fn mesh<N: Vertex, C: Edge + std::fmt::Debug>(dims: &[usize]) -> Topology<N, C> {
        let mut topo = Topology::new(TopologyType::Mesh(Self {
            dims: dims.to_vec(),
        }));

        // node ids are from 1 to mesh.mesh_x * mesh_y + 1
        for _ in 0..dims.iter().product() {
            topo.add_node(N::new_vertex());
        }
        // build the links: for each node, add the connections to their
        // "higher" node pairs.
        for e in dims.iter().map(|&d| 0..d).multi_cartesian_product() {
            // e is a vector that contains the coordinates of a node
            for (d, &m) in dims.iter().enumerate() {
                let mut n = e.clone();
                if (e[d] + 1) < m {
                    n[d] = e[d] + 1;
                    topo.add_link(C::new_edge(
                        topo.node(linearize_index(dims, &e)).id(),
                        topo.node(linearize_index(dims, &n)).id(),
                    ));
                }
            }
        }
        topo
    }

    pub fn name(&self) -> String {
        format!(
            "Mesh {}D ({})",
            self.dims.len(),
            itertools::join(&self.dims, " x ")
        )
    }
}

impl Layout2D for Mesh {
    /// The X extent in a virtual canvas
    fn get_max_x(&self) -> usize {
        if self.dims.len() > 2 {
            let num_nodes: usize = self.dims.iter().product();
            (num_nodes as f64).sqrt().ceil() as usize
        } else {
            self.dims[0]
        }
    }
    /// The Y extent in a virtual canvas
    fn get_max_y(&self) -> usize {
        if self.dims.len() > 2 {
            let num_nodes: usize = self.dims.iter().product();
            (num_nodes - 1) / self.get_max_x() + 1
        } else {
            self.dims[1]
        }
    }
    /// Node coordinates in a the virtual canvas
    fn get_node_coordinates(&self, node_id: NodeId) -> Coordinates {
        Coordinates::new(node_id % self.get_max_x(), node_id / self.get_max_x())
    }
}

#[cfg(test)]
mod tests {
    use crate::layout::{Coordinates, Layout2D};
    use crate::mesh::Mesh;
    use crate::tests::{count_connections, Connection, Node};
    use crate::Topology;
    use crate::Vertex;
    use itertools::Itertools;

    #[test]
    fn test_mesh2d() {
        let (x, y) = (4, 3);
        let topo: Topology<Node, Connection> = Mesh::mesh(&vec![x, y]);
        assert_eq!(topo.nodes().count(), x * y);
        assert_eq!(topo.connections().count(), 17);

        let node_11 = topo.node(5); // node at coords (1,1) is a fully connected node
        println!("Node id: {}", node_11.id());
        println!("Topology:\n{}", topo);
        println!(
            "\nNode {} connections:\n{:?}",
            node_11.id(),
            topo.node_connections(&node_11.id()).format("\n")
        );
        assert_eq!(count_connections(node_11.id(), &topo), 4);
        assert_eq!(count_connections(topo.node(1).id(), &topo), 3); // (1, 0) has 3
        assert_eq!(count_connections(topo.node(3 * 4 - 1).id(), &topo), 2);
        // (3, 2) has 2
    }

    #[test]
    fn test_mesh3d() {
        let (x, y, z) = (4, 3, 3);
        let topo: Topology<Node, Connection> = Mesh::mesh(&vec![x, y, z]);
        assert_eq!(topo.nodes().count(), x * y * z);
        assert_eq!(topo.connections().count(), 3 * 17 + 2 * 12);

        let node_111 = topo.node(x * y + x + 1); // node at coords (1,1,1) is a fully connected node
        println!("Node id: {}", node_111.id());
        println!("Topology: {}", topo);
        println!(
            "\nNode {} connections:\n{:?}",
            node_111.id(),
            topo.node_connections(&node_111.id()).format("\n")
        );
        assert_eq!(count_connections(node_111.id(), &topo), 6);
        assert_eq!(count_connections(topo.node(x + 1).id(), &topo), 5); // (1, 1, 0) has 5
        assert_eq!(count_connections(topo.node(1).id(), &topo), 4); // (1, 0, 0) has 4
        assert_eq!(count_connections(topo.node(x * y - 1).id(), &topo), 3); // (3, 2, 0) has 3
    }

    #[test]
    fn test_mesh2d_layout() {
        let (x, y) = (5, 3);
        let topo: Topology<Node, Connection> = Mesh::mesh(&vec![x, y]);
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
}
