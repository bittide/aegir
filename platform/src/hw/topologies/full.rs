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
use super::{validate_configurations, PortConfiguration};
use crate::calendar::Buffering;
use crate::hw::{ComputeNode, Link};
use crate::HardwareSpecType;
use crate::Port;
use crate::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};
use petgraph::graph::node_index;

/// A fully connected topology of `nodes` size (no switches).
///
/// It represents a topology in which each node is connected to every
/// other node.
pub fn fully_connected<const BUFFERING: Buffering>(
    num_nodes: usize,
    compute_config: &NodeConfiguration,
    _switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    validate_configurations(compute_config, None, link_config);

    let port_config = PortConfiguration::from_link_config(link_config);

    // a map to remember the last port assigned for each node.
    let mut port_alloc = PortAllocator::new();

    let mut hw_spec = HardwareSpecType::new();
    let mut node_config = compute_config.clone();
    for n in 0..num_nodes - 1 {
        node_config.add_link(&link_config, Port::new(n, &port_config.incoming));
        node_config.add_link(&link_config, Port::new(n, &port_config.outgoing));
    }

    for n in 0..num_nodes {
        let node_id = hw_spec.add_node(
            ComputeNode::from_config(format!("node_{}", n).as_str(), &node_config).into(),
        );

        for peer in 0..n {
            let peer_id = node_index(peer);
            let src_port = port_alloc.get_next(node_id);
            let dst_port = port_alloc.get_next(peer_id);

            hw_spec.link_simplex(
                node_id,
                peer_id,
                Link::from_config(src_port, dst_port, *link_config),
            );
            hw_spec.link_simplex(
                peer_id,
                node_id,
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

    #[test]
    fn test_fully_connected() {
        let _logger = env_logger::builder().try_init();
        let num_nodes = 5;
        let topo = fully_connected::<{ BUFFERING_DOUBLE }>(
            num_nodes,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );

        assert_eq!(topo.compute_nodes().len(), num_nodes);
        assert_eq!(topo.iter_nodes().count(), num_nodes);

        let num_conns = num_nodes - 1;
        for n in topo.iter_nodes() {
            assert_eq!(topo.get_node_inout_count(n), (num_conns, num_conns));
        }
        log::debug!("Topology:\n{}", topo);
    }
}
