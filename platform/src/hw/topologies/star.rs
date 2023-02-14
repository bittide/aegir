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
use crate::hw::{ComputeNode, Link, SwitchNode};
use crate::HardwareSpecType;
use crate::Port;
use crate::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};

/// generate a Star topology of hosts compute nodes + 1 hub switch node
pub fn star<const BUFFERING: Buffering>(
    hosts: usize,
    compute_config: &NodeConfiguration,
    switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    validate_configurations(compute_config, Some(switch_config), link_config);

    let port_config = PortConfiguration::from_link_config(link_config);

    let mut hw_spec = HardwareSpecType::new();
    let mut node_config = compute_config.clone();
    node_config.add_link(&link_config, Port::new(0, &port_config.incoming));
    node_config.add_link(&link_config, Port::new(0, &port_config.outgoing));

    let switch_id = hw_spec.add_node(
        SwitchNode::from_config(
            format!("hub").as_str(),
            &SwitchConfiguration {
                input_link_count: hosts,
                output_link_count: hosts,
                ..*switch_config
            },
        )
        .into(),
    );
    for n in 0..hosts {
        let node_id = hw_spec.add_node(
            ComputeNode::from_config(format!("node_{}", n).as_str(), &node_config).into(),
        );
        // input link
        hw_spec.link_simplex(switch_id, node_id, Link::from_config(n, 0, *link_config));
        // output link
        hw_spec.link_simplex(node_id, switch_id, Link::from_config(0, n, *link_config));
    }

    hw_spec
}

#[cfg(test)]
mod topology_tests {
    use super::*;
    use crate::calendar::BUFFERING_DOUBLE;
    use petgraph::graph::node_index;

    #[test]
    fn test_star() {
        let _logger = env_logger::builder().try_init();
        let hosts = 5;
        let topo = star::<{ BUFFERING_DOUBLE }>(
            hosts,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        assert_eq!(topo.compute_nodes().len(), hosts);
        assert_eq!(topo.iter_nodes().count(), hosts + 1);

        for n in topo.compute_nodes().iter() {
            assert_eq!(topo.get_node_inout_count(*n), (1, 1));
        }
        assert_eq!(topo.get_node_inout_count(node_index(0)), (hosts, hosts));
        log::debug!("Topology:\n{}", topo);
    }
}
