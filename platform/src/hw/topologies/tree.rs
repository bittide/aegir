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
use crate::NodeIndex;
use crate::Port;
use crate::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};
use petgraph::graph::node_index;

/// A tree toplogy
///
/// # Example
///
/// A ternary-tree of height 3:
/// <pre>
///           0
///   1       2         3
/// 4 5 6   7 8 9   10 11 12
/// </pre>
/// We build the root as a switch, all other nodes are compute nodes.
/// For a topology where only the leaf nodes are compute, see `fat_tree`.
pub fn tree<const BUFFERING: Buffering>(
    height: usize,
    children: usize,
    compute_config: &NodeConfiguration,
    switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    validate_configurations(compute_config, Some(switch_config), link_config);

    let port_config = PortConfiguration::from_link_config(link_config);

    let num_nodes = ((1 - (children as i32).pow(height as u32)) / (1 - children as i32)) as usize;
    // store the index of the node returned by the system so that we can retrieve
    // them to add links
    let mut nodes = (0..num_nodes)
        .map(|_| node_index(0))
        .collect::<Vec<NodeIndex>>();

    let mut hw_spec = HardwareSpecType::new();
    let mut node_config = compute_config.clone();
    for n in 0..children + 1 {
        node_config.add_link(&link_config, Port::new(n, &port_config.incoming));
        node_config.add_link(&link_config, Port::new(n, &port_config.outgoing));
    }

    // add the root as a switch
    nodes[0] = hw_spec.add_node(
        SwitchNode::from_config(
            format!("root").as_str(),
            &SwitchConfiguration {
                input_link_count: children,
                output_link_count: children,
                ..*switch_config
            },
        )
        .into(),
    );

    let mut prev_nodes = 0;
    for level in 1..(height as u32) {
        prev_nodes += children.pow(level - 1);
        for child in 0..children.pow(level) {
            let child_id = hw_spec.add_node(
                ComputeNode::from_config(
                    format!("node_{}", child + prev_nodes).as_str(),
                    &node_config,
                )
                .into(),
            );
            nodes[child + prev_nodes] = child_id;
            let parent_id = nodes[(child / children) + prev_nodes - children.pow(level - 1)];
            hw_spec.link_simplex(
                child_id,
                parent_id,
                Link::from_config(0, child, *link_config),
            );
            hw_spec.link_simplex(
                parent_id,
                child_id,
                Link::from_config(child, 0, *link_config),
            );
        }
    }

    hw_spec
}

#[cfg(test)]
mod topology_tests {
    use super::*;
    use crate::calendar::BUFFERING_DOUBLE;

    fn is_leaf(node_id: usize, height: usize, children: usize) -> bool {
        let num_internal =
            ((1 - (children as i32).pow(height as u32 - 1)) / (1 - children as i32)) as usize;
        node_id >= num_internal
    }

    fn validate_tree(
        height: usize,
        children: usize,
        topo: &HardwareSpecType<{ BUFFERING_DOUBLE }>,
    ) {
        let num_nodes =
            ((1 - (children as i32).pow(height as u32)) / (1 - children as i32)) as usize;
        let num_conns = 2 * (num_nodes - 1);
        assert_eq!(topo.compute_nodes().len(), num_nodes - 1);
        assert_eq!(topo.iter_nodes().count(), num_nodes);
        assert_eq!(topo.iter_links().count(), num_conns);
        for n in topo.iter_nodes() {
            if n.index() == 0 {
                // root
                assert_eq!(topo.get_node_inout_count(n), (children, children));
            } else if is_leaf(n.index(), height, children) {
                assert_eq!(topo.get_node_inout_count(n), (1, 1));
            } else {
                assert_eq!(topo.get_node_inout_count(n), (children + 1, children + 1),);
            }
        }
    }

    #[test]
    fn test_binary_tree() {
        let _logger = env_logger::builder().try_init();
        let (height, children) = (4, 2);
        let topo = tree::<{ BUFFERING_DOUBLE }>(
            height,
            children,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        log::debug!("Topology: {}", topo);
        validate_tree(height, children, &topo);
    }

    #[test]
    fn test_ternary_tree() {
        let _logger = env_logger::builder().try_init();
        let (height, children) = (4, 3);
        let topo = tree::<{ BUFFERING_DOUBLE }>(
            height,
            children,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        log::debug!("Topology: {}", topo);
        validate_tree(height, children, &topo);
    }
}
