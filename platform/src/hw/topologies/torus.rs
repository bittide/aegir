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

pub fn torus<const BUFFERING: Buffering>(
    dims: &[usize],
    compute_config: &NodeConfiguration,
    _switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    validate_configurations(compute_config, None, link_config);

    let port_config = PortConfiguration::from_link_config(link_config);

    let mut hw_spec = HardwareSpecType::new();
    // store the index of the node returned by the system so that we can retrieve
    // them to add links
    let mut nodes = Vec::new();
    let mut port_alloc = PortAllocator::new();

    let mut node_config = compute_config.clone();
    for port in 0..(2 * dims.len()) {
        node_config.add_link(&link_config, Port::new(port, &port_config.incoming));
        node_config.add_link(&link_config, Port::new(port, &port_config.outgoing));
    }

    for n in 0..dims.iter().product() {
        let node_id = hw_spec.add_node(
            ComputeNode::from_config(format!("node_{}", n).as_str(), &node_config).into(),
        );
        nodes.push(node_id);
    }

    // build the links: for each node, add the connections to their
    // "higher" node pairs.
    for e in dims.iter().map(|&ub| 0..ub).multi_cartesian_product() {
        // e is a vector that contains the coordinates of a node
        for (d, m) in dims.iter().enumerate() {
            let mut n = e.clone();
            n[d] = (e[d] + 1) % m;

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

    hw_spec
}

#[cfg(test)]
mod topology_tests {
    use super::*;
    use crate::calendar::BUFFERING_DOUBLE;
    use crate::NodeSpec;
    use petgraph::graph::node_index;
    use std::convert::TryInto;

    #[test]
    fn test_torus() {
        let _logger = env_logger::builder().try_init();
        let (x, y, z) = (3, 4, 3);
        let dims = vec![x, y, z];
        let topo = torus::<{ BUFFERING_DOUBLE }>(
            &dims,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        assert_eq!(topo.compute_nodes().len(), x * y * z);
        assert_eq!(topo.iter_nodes().count(), x * y * z);

        for n in topo.iter_nodes() {
            assert_eq!(topo.get_node_inout_count(n), (6, 6));
        }
        let index = node_index(linearize_index(&[1, 1, 1], &dims));
        let node = topo.get_node(index);

        /*
          0  1  2    12 13 14    24 25 26
          3  4  5    15 *16 17   27 28 29
          6  7  8    18 19 20    30 31 32
          9 10 11    21 22 23    33 34 35

         16 is connected to 15, 17, 13, 19, 4, 28
        */
        log::debug!(
            "\nNode {} connections:\n\tInput:\n\t{:?}\n\tOutput:\n\t{:?}",
            node.borrow().name(),
            topo.get_input_links(index).format("\n\t"),
            topo.get_output_links(index).format("\n\t"),
        );

        let neighbors = [
            [0, 1, 1],
            [2, 1, 1],
            [1, 0, 1],
            [1, 2, 1],
            [1, 1, 0],
            [1, 1, 2],
        ];
        for n in topo.neighbors(index) {
            let e = delinearize_index(n.index(), &dims);
            log::debug!("\tneighbor: {:?}", e);
            assert!(neighbors.contains(&e.try_into().unwrap()));
        }
    }
}
