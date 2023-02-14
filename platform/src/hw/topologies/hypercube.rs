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

/// A hypercube topology
///
/// Building a hypecube will result in a topology with 2^degree nodes.
pub fn hypercube<const BUFFERING: Buffering>(
    degree: usize,
    compute_config: &NodeConfiguration,
    _switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    validate_configurations(compute_config, None, link_config);

    let port_config = PortConfiguration::from_link_config(link_config);

    let num_nodes = 2_usize.pow(degree as u32);

    let mut hw_spec = HardwareSpecType::new();
    let mut node_config = compute_config.clone();
    for n in 0..degree {
        node_config.add_link(&link_config, Port::new(n, &port_config.incoming));
        node_config.add_link(&link_config, Port::new(n, &port_config.outgoing));
    }
    // store the index of the node returned by the system so that we can retrieve
    // them to add links
    let nodes = (0..num_nodes)
        .map(|n| {
            hw_spec.add_node(
                ComputeNode::from_config(format!("node_{}", n).as_str(), &node_config).into(),
            )
        })
        .collect::<Vec<_>>();

    // a map to remember the last port assigned for each node.
    let mut port_alloc = PortAllocator::new();

    // build the links: for each node, add the connections to their
    // "higher" node peers, that is connect the bit 0s to the bit 1s
    for n in 0..num_nodes {
        for b in 0..degree {
            if (n & (1 << b)) == 0 {
                log::debug!(
                    "Linking node {:0width$b} with {:0width$b}",
                    n,
                    (n | (1 << b)),
                    width = degree
                );
                let node_id = nodes[n];
                let peer_id = nodes[n | (1 << b)];
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
    }
    hw_spec
}

#[cfg(test)]
mod topology_tests {
    use super::*;
    use crate::calendar::BUFFERING_DOUBLE;

    #[test]
    fn test_hypercube() {
        let _logger = env_logger::builder().try_init();
        let degree = 4;
        let num_nodes = 2_usize.pow(degree as u32);
        let topo = hypercube::<{ BUFFERING_DOUBLE }>(
            degree,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );

        assert_eq!(topo.compute_nodes().len(), num_nodes);
        assert_eq!(topo.iter_nodes().count(), num_nodes);
        assert_eq!(
            topo.iter_links().count(),
            2_usize.pow(degree as u32) * degree // each node has degree links in each direction
        );
        for n in topo.iter_nodes() {
            assert_eq!(topo.get_node_inout_count(n), (degree, degree));
        }
        log::debug!("Topology:\n{}", topo);
    }
}
