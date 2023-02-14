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

use super::{validate_configurations, PortConfiguration};
use crate::calendar::Buffering;
use crate::hw::{ComputeNode, Link};
use crate::HardwareSpecType;
use crate::Port;
use crate::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};

/// generate a line topology (no switches).
///
/// An unrealistic topology that we can use to test latency.
/// The network diameter determines the latency of seeing changes across the network, and line
/// is easy to reason about.
pub fn line<const BUFFERING: Buffering>(
    num_nodes: usize,
    compute_config: &NodeConfiguration,
    _switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    validate_configurations(compute_config, None, link_config);

    let port_config = PortConfiguration::from_link_config(link_config);

    let mut hw_spec = HardwareSpecType::new();
    let mut end_node_config = compute_config.clone();
    end_node_config.add_link(&link_config, Port::new(0, &port_config.incoming));
    end_node_config.add_link(&link_config, Port::new(0, &port_config.outgoing));
    let mut node_config = end_node_config.clone();
    node_config.add_link(&link_config, Port::new(1, &port_config.incoming));
    node_config.add_link(&link_config, Port::new(1, &port_config.outgoing));

    let mut prev_id = hw_spec
        .add_node(ComputeNode::from_config(format!("node_0",).as_str(), &end_node_config).into());

    for n in 1..num_nodes-1 {
        let node_id = hw_spec.add_node(
            ComputeNode::from_config(format!("node_{}", n).as_str(), &node_config).into(),
        );

        // input link
        hw_spec.link_simplex(prev_id, node_id, Link::from_config(0, 1, *link_config));
        // output link
        hw_spec.link_simplex(node_id, prev_id, Link::from_config(1, 0, *link_config));

        prev_id = node_id;
    }
    let last_id = hw_spec
        .add_node(ComputeNode::from_config(format!("node_0",).as_str(), &end_node_config).into());
    hw_spec.link_simplex(prev_id, last_id, Link::from_config(0, 0, *link_config));
    hw_spec.link_simplex(last_id, prev_id, Link::from_config(0, 0, *link_config));

    hw_spec
}

#[cfg(test)]
mod topology_tests {
    use super::*;
    use crate::calendar::BUFFERING_DOUBLE;
    use petgraph::graph::node_index;

    #[test]
    fn test_line() {
        let _logger = env_logger::builder().try_init();
        let num_nodes = 5;
        let topo = line::<{ BUFFERING_DOUBLE }>(
            num_nodes,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        assert_eq!(topo.compute_nodes().len(), num_nodes);
        assert_eq!(topo.iter_nodes().count(), num_nodes);

        assert_eq!(topo.get_node_inout_count(node_index(0)), (1, 1));
        (1..num_nodes-1).for_each(|n| {
            assert_eq!(topo.get_node_inout_count(node_index(n)), (2, 2));
        });
        assert_eq!(topo.get_node_inout_count(node_index(num_nodes - 1)), (1, 1));
        log::debug!("Topology:\n{}", topo);
    }
}
