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

use super::PortAllocator;
use super::{delinearize_index, linearize_index};
use super::{validate_configurations, PortConfiguration};
use crate::calendar::Buffering;
use crate::hw::ComputeNode;
use crate::hw::Link;
use crate::HardwareSpecType;
use crate::Port;
use crate::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};
use itertools::Itertools;

/// test whether the node is a corner
fn is_corner(elem: &[usize], dims: &[usize]) -> bool {
    // coordinates in all dimensions should be either 0 or max
    elem.iter()
        .enumerate()
        .all(|(d, &v)| v == 0 || v == dims[d] - 1)
}

/// test whether the node is a border
fn is_border(elem: &[usize], dims: &[usize]) -> bool {
    if is_corner(&elem, &dims) {
        return false;
    }
    // coordinates in all but one dimension should be either 0 or max.
    elem.iter()
        .enumerate()
        .filter(|(d, &v)| v == 0 || v == dims[*d] - 1)
        .count()
        == dims.len() - 1
}

/// A <dim>-D grid topology with no switches.
///
/// All the links have the same properties (frame size, latency, etc.).
///
/// Nodes are homogeneous, they all have the same computational characteristics,
/// as defined in  compute_config. compute_config should not have any links
/// specified.
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
pub fn mesh<const BUFFERING: Buffering>(
    dims: &[usize],
    compute_config: &NodeConfiguration,
    _switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    validate_configurations(compute_config, None, link_config);

    let port_config = PortConfiguration::from_link_config(link_config);

    let mut hw_spec = HardwareSpecType::new();
    // store the index of the node returned by hw_spec so that we can retrieve
    // them to add links
    let mut nodes = Vec::new();
    // a map to remember the last port assigned for each node. Depending of which
    // node this is in the mesh, the port assignment will vary, even though links
    // are set always my the node with the smaller id. When a node's turn comes, the
    // node needs to remember how many it has already been assigned.
    let mut port_alloc = PortAllocator::new();

    // a corner node has len(dims) edges
    let mut corner_config = compute_config.clone();
    for port in 0..dims.len() {
        corner_config.add_link(&link_config, Port::new(port, &port_config.incoming));
        corner_config.add_link(&link_config, Port::new(port, &port_config.outgoing));
    }
    // a border link has 2 * len(dims) - 1 edges
    let mut border_config = compute_config.clone();
    for port in 0..(2 * dims.len() - 1) {
        border_config.add_link(&link_config, Port::new(port, &port_config.incoming));
        border_config.add_link(&link_config, Port::new(port, &port_config.outgoing));
    }

    // a middle node has all 2 * len(dims) edges
    let mut middle_config = compute_config.clone();
    for port in 0..(2 * dims.len()) {
        middle_config.add_link(&link_config, Port::new(port, &port_config.incoming));
        middle_config.add_link(&link_config, Port::new(port, &port_config.outgoing));
    }

    for n in 0..dims.iter().product() {
        let e = delinearize_index(n, dims);
        let name = format!("node_{}", n);
        log::debug!("node {}, index {}, coords {:?}", name, n, e);
        let config = if is_corner(&e, dims) {
            &corner_config
        } else if is_border(&e, dims) {
            &border_config
        } else {
            &middle_config
        };
        let node_id = hw_spec.add_node(ComputeNode::from_config(name.as_str(), &config).into());
        nodes.push(node_id);
    }

    // build the links: for each node, add the connections to their
    // "higher" node pairs.
    for e in dims.iter().map(|&d| 0..d).multi_cartesian_product() {
        // e is a vector that contains the coordinates of a node
        for (d, &m) in dims.iter().enumerate() {
            let mut n = e.clone();
            if (e[d] + 1) < m {
                n[d] = e[d] + 1;

                let src = nodes[linearize_index(&e, dims)];
                let dst = nodes[linearize_index(&n, dims)];

                let src_port = port_alloc.get_next(src);
                let dst_port = port_alloc.get_next(dst);

                // all the links are bidirectional
                hw_spec.link_simplex(
                    src,
                    dst,
                    Link::from_config(src_port, dst_port, *link_config),
                );
                hw_spec.link_simplex(
                    dst,
                    src,
                    Link::from_config(dst_port, src_port, *link_config),
                );
            }
        }
    }

    hw_spec
}

#[cfg(test)]
mod topology_tests {
    use super::*;
    use crate::calendar::BUFFERING_DOUBLE;
    use crate::NodeSpec;
    use petgraph::graph::node_index;

    #[test]
    fn test_is_corner() {
        fn validate_corners(dims: &[usize], corners: &[Vec<usize>]) {
            for e in dims.iter().map(|&d| 0..d).multi_cartesian_product() {
                if is_corner(&e, &dims) {
                    assert!(corners.contains(&e), "{:?} is not a corner", e);
                } else {
                    assert!(!corners.contains(&e), "{:?} should not be a corner", e);
                }
            }
        }
        validate_corners(
            &[2, 2],
            &vec![vec![0, 0], vec![0, 1], vec![1, 0], vec![1, 1]],
        );
        validate_corners(
            &vec![5, 5],
            &vec![vec![0, 0], vec![0, 4], vec![4, 0], vec![4, 4]],
        );
        validate_corners(
            &vec![5, 5, 2],
            &vec![
                vec![0, 0, 0],
                vec![0, 4, 0],
                vec![0, 0, 1],
                vec![0, 4, 1],
                vec![4, 0, 0],
                vec![4, 4, 0],
                vec![4, 0, 1],
                vec![4, 4, 1],
            ],
        );
    }
    #[test]
    fn test_is_border() {
        fn validate_borders(dims: &[usize], borders: &[Vec<usize>]) {
            for e in dims.iter().map(|&d| 0..d).multi_cartesian_product() {
                if is_border(&e, &dims) {
                    assert!(borders.contains(&e), "{:?} is not a border", e);
                } else {
                    assert!(!borders.contains(&e), "{:?} should not be a border", e);
                }
            }
        }
        validate_borders(&[2, 2], &vec![]);
        validate_borders(&[3, 2], &vec![vec![1, 0], vec![1, 1]]);
        validate_borders(
            &vec![4, 4],
            &vec![
                vec![0, 1],
                vec![0, 2],
                vec![1, 0],
                vec![2, 0],
                vec![3, 1],
                vec![3, 2],
                vec![1, 3],
                vec![2, 3],
            ],
        );
        validate_borders(
            &vec![5, 5, 3],
            &vec![
                vec![1, 0, 0],
                vec![2, 0, 0],
                vec![3, 0, 0],
                vec![1, 4, 0],
                vec![2, 4, 0],
                vec![3, 4, 0],
                vec![1, 0, 2],
                vec![2, 0, 2],
                vec![3, 0, 2],
                vec![1, 4, 2],
                vec![2, 4, 2],
                vec![3, 4, 2],
                vec![0, 0, 1],
                vec![4, 0, 1],
                vec![0, 4, 1],
                vec![4, 4, 1],
                vec![0, 1, 0],
                vec![0, 2, 0],
                vec![0, 3, 0],
                vec![4, 1, 0],
                vec![4, 2, 0],
                vec![4, 3, 0],
                vec![0, 1, 2],
                vec![0, 2, 2],
                vec![0, 3, 2],
                vec![4, 1, 2],
                vec![4, 2, 2],
                vec![4, 3, 2],
            ],
        );
    }

    #[test]
    fn test_mesh2d() {
        let _logger = env_logger::builder().try_init();
        let (x, y) = (4, 3);
        let dims = vec![x, y];
        let topo = mesh::<{ BUFFERING_DOUBLE }>(
            &dims,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        assert_eq!(topo.compute_nodes().len(), x * y);
        assert_eq!(topo.iter_nodes().count(), x * y);
        let corners = 2_usize.pow(dims.len() as u32);
        let borders = dims.len() * (dims.iter().sum::<usize>() - corners);
        let middle: usize = dims.iter().map(|&ub| ub - 2).product();
        assert_eq!(
            topo.iter_links().count(),
            (corners * 2 + borders * 3 + middle * 4)
        );

        // node at coords (1,1) is a fully connected node
        let index = node_index(linearize_index(&[1, 1], &dims));
        let node = topo.get_node(index);
        log::debug!(
            "\nNode {} connections:\n\tInput:\n\t{:?}\n\tOutput:\n\t{:?}",
            node.borrow().name(),
            topo.get_input_links(index).format("\n\t"),
            topo.get_output_links(index).format("\n\t"),
        );
        assert_eq!(topo.get_node_inout_count(index), (4, 4));
        for e in dims.iter().map(|&d| 0..d).multi_cartesian_product() {
            let conns = topo.get_node_inout_count(node_index(linearize_index(&e, &dims)));
            if is_corner(&e, &dims) {
                assert_eq!(conns, (2, 2));
            } else if is_border(&e, &dims) {
                assert_eq!(conns, (3, 3));
            } else {
                assert_eq!(conns, (4, 4));
            }
        }
        log::debug!("Topology:\n{}", topo);
    }

    #[test]
    fn test_mesh3d() {
        let _logger = env_logger::builder().try_init();
        let (x, y, z) = (4, 3, 3);
        let dims = vec![x, y, z];
        let topo = mesh::<{ BUFFERING_DOUBLE }>(
            &dims,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        assert_eq!(topo.compute_nodes().len(), x * y * z);
        assert_eq!(topo.iter_links().count(), 2 * (y * 17 + (z - 1) * 12));

        // node at coords (1,1,1) is a fully connected node
        let index = node_index(linearize_index(&[1, 1, 1], &dims));
        let node = topo.get_node(index);
        log::debug!(
            "\nNode {} connections:\n\tInput:\n\t{:?}\n\tOutput:\n\t{:?}",
            node.borrow().name(),
            topo.get_input_links(index).format("\n\t"),
            topo.get_output_links(index).format("\n\t"),
        );
        assert_eq!(topo.get_node_inout_count(index), (6, 6));
        assert_eq!(
            topo.get_node_inout_count(node_index(linearize_index(&[1, 1, 0], &dims))),
            (5, 5) // (1, 1, 0) has 5
        );
        assert_eq!(
            topo.get_node_inout_count(node_index(linearize_index(&[1, 0, 0], &dims))),
            (4, 4) // (1, 0, 0) has 4
        );
        assert_eq!(
            topo.get_node_inout_count(node_index(linearize_index(&[x - 1, 0, 0], &dims))),
            (3, 3) // corner has 3
        );
    }

    #[test]
    fn test_mesh4d() {
        let _logger = env_logger::builder().try_init();
        let (x, y, z, w) = (4, 3, 3, 3);
        let dims = vec![x, y, z, w];
        let topo = mesh::<{ BUFFERING_DOUBLE }>(
            &dims,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        assert_eq!(topo.compute_nodes().len(), x * y * z * w);
        // node at coords (1,1,1,1) is a fully connected node
        let index = node_index(linearize_index(&[1, 1, 1, 1], &dims));
        let node = topo.get_node(index);
        log::debug!(
            "\nNode {} connections:\n\tInput:\n\t{:?}\n\tOutput:\n\t{:?}",
            node.borrow().name(),
            topo.get_input_links(index).format("\n\t"),
            topo.get_output_links(index).format("\n\t"),
        );
        assert_eq!(topo.get_node_inout_count(index), (8, 8));
        assert_eq!(
            topo.get_node_inout_count(node_index(linearize_index(&[x - 1, 0, 0, 0], &dims))),
            (4, 4)
        );
        assert_eq!(
            topo.get_node_inout_count(node_index(linearize_index(&[1, 0, 0, 0], &dims))),
            (5, 5)
        );
        assert_eq!(
            topo.get_node_inout_count(node_index(linearize_index(&[1, 1, 0, 0], &dims))),
            (6, 6)
        );
        assert_eq!(
            topo.get_node_inout_count(node_index(linearize_index(&[1, 1, 1, 0], &dims))),
            (7, 7)
        );
    }
}
