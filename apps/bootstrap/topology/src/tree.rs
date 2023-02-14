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
use serde::{Deserialize, Serialize};

/// A tree toplogy
///
/// # Example
///
/// A two-depth ternary-tree:
/// <pre>
///           0
///   1       2         3
/// 4 5 6   7 8 9   10 11 12
/// </pre>
#[derive(Serialize, Deserialize, Debug)]
pub struct Tree {
    /// tree height
    height: usize,
    /// number of children for an n-ary tree
    children: usize,
}

impl Tree {
    /// The n-ary tree builder
    ///
    /// Note that this builder will construct the entire tree, i.e., all
    /// children present for each parent.
    pub fn tree<N, C>(height: usize, children: usize) -> Topology<N, C>
    where
        N: Vertex,
        C: Edge + std::fmt::Debug,
    {
        let mut topo = Topology::new(TopologyType::Tree(Self { height, children }));

        topo.add_node(N::new_vertex()); // the root

        let mut prev_nodes = 0;
        for level in 1..(height as u32) {
            // println!("Level {}", level);
            prev_nodes += children.pow(level - 1);
            for c in 0..children.pow(level) {
                let child_id = c + prev_nodes;
                let parent_id = (c / children) + prev_nodes - children.pow(level - 1);
                // println!("Linking node {} with {}", parent_id, child_id);
                topo.add_node(N::new_vertex());
                topo.add_link(C::new_edge(
                    topo.node(parent_id).id(),
                    topo.node(child_id).id(),
                ));
            }
        }
        topo
    }

    pub fn name(&self) -> String {
        format!("Tree ({} x {})", self.height, self.children)
    }
}

impl Layout2D for Tree {
    /// The X extent in a virtual canvas: the number of children at the bottom level
    fn get_max_x(&self) -> usize {
        self.children.pow(self.height as u32 - 1)
    }
    /// The Y extent in a virtual canvas: the tree height
    fn get_max_y(&self) -> usize {
        self.height
    }
    /// Node coordinates in a the virtual canvas
    fn get_node_coordinates(&self, node_id: NodeId) -> Coordinates {
        let node_depth = (((node_id * (self.children - 1)) as f64).log2()
            / (self.children as f64).log2())
        .floor() as u32;
        let nodes_at_prev_depth = ((1.0 - (self.children.pow(node_depth) as f64))
            / (1.0 - self.children as f64))
            .ceil() as usize;
        let x = node_id - nodes_at_prev_depth - 1;
        let y = node_depth as usize;
        Coordinates::new(x, y)
    }
}

#[cfg(test)]
mod tests {
    use crate::layout::{Coordinates, Layout2D};
    use crate::tests::{count_connections, Connection, Node};
    use crate::tree::Tree;
    use crate::Topology;
    use crate::Vertex;

    #[test]
    fn test_binary_tree() {
        let (height, children) = (4, 2);
        let topo: Topology<Node, Connection> = Tree::tree(height, children);
        println!("Topology: {:?}", topo);
        assert_eq!(topo.nodes().count(), 2usize.pow(height as u32) - 1);
        assert_eq!(topo.connections().count(), 2usize.pow(height as u32) - 2); // 2^k-1 - 1

        let node_r = topo.node(2); // right child of root -- must have 3 connections
        assert_eq!(count_connections(node_r.id(), &topo), 3);
        assert_eq!(count_connections(topo.node(0).id(), &topo), 2); // root has only 2
    }

    #[test]
    fn test_ternary_tree() {
        let (height, children) = (4, 3);
        let topo: Topology<Node, Connection> = Tree::tree(height, children);
        println!("Topology: {:?}", topo);
        let total_nodes =
            ((1 - (children as i32).pow(height as u32)) / (1 - children as i32)) as usize;
        assert_eq!(topo.nodes().count(), total_nodes);
        assert_eq!(topo.connections().count(), (total_nodes - 1));

        let node_r = topo.node(2);
        // root has `children` connections
        assert_eq!(count_connections(topo.node(0).id(), &topo), children);
        // mid child of root -- must have `children + 1` connections (its children and parent)
        assert_eq!(count_connections(node_r.id(), &topo), children + 1);
        // leaves have only 1
        assert_eq!(count_connections(topo.node(total_nodes - 1).id(), &topo), 1);
    }

    /* switched to default layout: too many blank pages */
    #[test]
    #[ignore]
    fn test_tree_layout() {
        let (height, children) = (4, 3);
        let topo: Topology<Node, Connection> = Tree::tree(height, children);
        assert_eq!(topo.get_max_x(), 27, "Invalid x-extent");
        assert_eq!(topo.get_max_y(), 4, "Invalid y-extent");
        assert_eq!(
            topo.get_node_coordinates(topo.node(0).id()),
            Coordinates::new(0, 0),
            "Invalid node 1 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(3).id()),
            Coordinates::new(2, 1),
            "Invalid node 4 coordinates"
        );
        assert_eq!(
            topo.get_node_coordinates(topo.node(12).id()),
            Coordinates::new(8, 2),
            "Invalid node 13 coordinates"
        );
    }
}
