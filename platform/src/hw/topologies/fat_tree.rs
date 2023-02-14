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

use super::PortConfiguration;
use crate::calendar::Buffering;
use crate::hw::ComputeNode;
use crate::hw::Link;
use crate::hw::SwitchNode;
use crate::HardwareSpecType;
use crate::Port;
use crate::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};
use petgraph::prelude::*;

/// Generate a simple fat-tree HW topology: https://en.wikipedia.org/wiki/Fat_tree.
///
/// Define a edge-pair between nodes nodes n(i), n(j) as the edges n(i) ->
///   n(j), and n(j) -> n(i)
///
/// The fat-tree has a height H. The height of a fat-tree with a single
/// compute-node is 0 (this is a degenerate case).
///
/// A fat tree with height H has totals of,
///
///   nodes         : \sum_{i=0}^{H} 2^i = 2^{H+1} - 1
///   compute nodes : 2^H
///   switches      : 2^{H + 1} - 1 - 2^H = 2^H - 1
///
/// The root node of the fat-tree is at level L = H. The root's children are
/// at level L = H - 1, and so forth. The leaves of the fat-tree are at level
/// 0.
///
/// Only leaves in the fat tree are compute nodes, i.e., nodes at L=0.
/// Nodes at L > 0 are switch nodes.
///
/// A switch at level L has,
///   L edge-pairs to its left child
///   L edge-pairs to its right child
///
/// A switch at level L < H has,
///   2*L edge-pairs to its children
///   L+1 edge-pairs to its parent
///   2*(3*L + 1) input/output ports
///
/// The ports of a switch are organized as follows,
///   input/output ports  0..L         are connected to the left child,
///                       L..2*L       are connected to the right child,
///                       2*L..3*L + 1 are connected to the parent,
///
/// The root switch (L = H) has,
///   2*H edge-pairs to its children
///   2*H input/output ports
///
/// Example H = 2,
///
///   total nodes   : 2^(H + 1) - 1 = 7
///   compute nodes : 2^H = 4
///   switch nodes  : 2^H - 1 = 3
///
///```text
///                       switch_0_2,                            L = 2
///                       //     \\
///                      //       \\
///                     //         \\
///                    //           \\
///                   //             \\
///                  //               \\
///                 //                 \\
///                //                   \\
///               //                     \\
///              //                       \\
///             //                         \\
///         switch_0_1                   switch_1_1              L = 1
///         /       \                     /      \
///        /         \                   /        \
///       /           \                 /          \
///  compute_0     compute_1        compute_2    compute_3       L = 0
///```
/// compute_k_0 has: 1 input & 1 output port
/// switch_k_1  has: 4 input & 4 output ports
/// switch_k_2  has: 4 input & 4 output ports
pub fn fat_tree<const BUFFERING: Buffering>(
    height: usize,
    compute_config: &NodeConfiguration,
    switch_config: &SwitchConfiguration,
    link_config: &LinkConfiguration,
) -> HardwareSpecType<BUFFERING> {
    struct GenerateCounters {
        level: usize,
        index: usize,
        height: usize,
    }

    impl GenerateCounters {
        fn new(height: usize) -> Self {
            Self {
                level: height,
                index: 0,
                height: height,
            }
        }

        fn node_name(&self) -> String {
            if self.level == 0 {
                format!("compute_{}", self.index)
            } else {
                format!("switch_{}_{}", self.index, self.level)
            }
        }

        fn left(&self) -> Self {
            GenerateCounters {
                level: self.level - 1,
                index: 2 * self.index,
                ..*self
            }
        }

        fn right(&self) -> Self {
            GenerateCounters {
                level: self.level - 1,
                index: 2 * self.index + 1,
                ..*self
            }
        }

        fn port_count(&self) -> usize {
            if self.level == self.height {
                2 * self.level
            } else {
                3 * self.level + 1
            }
        }
    }

    fn fat_tree_rec<const BUFFERING: Buffering>(
        sys_spec: &mut HardwareSpecType<BUFFERING>,
        gen_counters: GenerateCounters,
        compute_config: &NodeConfiguration,
        switch_config: &SwitchConfiguration,
        link_config: &LinkConfiguration,
    ) -> NodeIndex {
        if gen_counters.level == 0 {
            return sys_spec.add_node(
                ComputeNode::from_config(gen_counters.node_name().as_str(), compute_config).into(),
            );
        }
        let left_child = fat_tree_rec(
            sys_spec,
            gen_counters.left(),
            compute_config,
            switch_config,
            link_config,
        );
        let right_child = fat_tree_rec(
            sys_spec,
            gen_counters.right(),
            compute_config,
            switch_config,
            link_config,
        );
        let port_count = gen_counters.port_count();
        let parent = sys_spec.add_node(
            SwitchNode::from_config(
                gen_counters.node_name().as_str(),
                &SwitchConfiguration {
                    input_link_count: port_count,
                    output_link_count: port_count,
                    ..*switch_config
                },
            )
            .into(),
        );

        let child_level = gen_counters.level - 1;
        let right_start = |level: usize| level;
        let parent_start = |level: usize| 2 * level;
        for k in 0..gen_counters.level {
            // Parent inputs from the left child.
            sys_spec.link_simplex(
                left_child,
                parent,
                Link::from_config(parent_start(child_level) + k, k, *link_config),
            );
            // Parent outputs to the left child.
            sys_spec.link_simplex(
                parent,
                left_child,
                Link::from_config(k, parent_start(child_level) + k, *link_config),
            );
            // Parent inputs from the right child.
            sys_spec.link_simplex(
                right_child,
                parent,
                Link::from_config(
                    parent_start(child_level) + k,
                    right_start(gen_counters.level) + k,
                    *link_config,
                ),
            );
            // Parent outputs to the right child.
            sys_spec.link_simplex(
                parent,
                right_child,
                Link::from_config(
                    right_start(gen_counters.level) + k,
                    parent_start(child_level) + k,
                    *link_config,
                ),
            );
        }
        parent
    }
    let mut sys_spec = HardwareSpecType::new();
    let gen_counters = GenerateCounters::new(height);

    let mut compute_config = compute_config.clone();
    let port_config = PortConfiguration::from_link_config(link_config);
    compute_config.add_link(&link_config, Port::new(0, &port_config.incoming));
    compute_config.add_link(&link_config, Port::new(0, &port_config.outgoing));

    fat_tree_rec(
        &mut sys_spec,
        gen_counters,
        &compute_config,
        switch_config,
        link_config,
    );
    sys_spec
}

#[cfg(test)]
mod topology_tests {
    use crate::calendar::BUFFERING_DOUBLE;

    use super::*;

    #[test]
    fn test_fat_tree() {
        let ft = fat_tree::<{ BUFFERING_DOUBLE }>(
            3,
            &NodeConfiguration::default(),
            &SwitchConfiguration::default(),
            &LinkConfiguration::default(),
        );
        assert_eq!(ft.compute_nodes().len(), 8);
        assert_eq!(ft.iter_nodes().count(), 15);
        assert_eq!(ft.iter_links().count(), 2 * (8 + 4 * 2 + 2 * 3));
    }
}
