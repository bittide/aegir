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

#![allow(dead_code)]
#![allow(unused_imports)]

use crate::PortProperties;
use crate::{LinkConfiguration, NodeConfiguration, SwitchConfiguration};
use petgraph::prelude::*;
use std::collections::HashMap;

mod fat_tree;
mod full;
mod hypercube;
mod line;
mod mesh;
mod star;
mod torus;
mod tree;

pub use fat_tree::fat_tree;
pub use full::fully_connected;
pub use hypercube::hypercube;
pub use line::line;
pub use mesh::mesh;
pub use star::star;
pub use torus::torus;
pub use tree::tree;

/// a map to remember the last port assigned for each node. Depending on a
/// node's position in the topology, the port assignment will vary.
struct PortAllocator {
    map: HashMap<NodeIndex, usize>,
}

impl PortAllocator {
    fn new() -> Self {
        Self {
            map: HashMap::new(),
        }
    }

    // return the next available port
    fn get_next(&mut self, node_id: NodeIndex) -> usize {
        let value = self.map.entry(node_id).or_insert(0);
        let port = *value;
        *value += 1;
        port
    }
}

/// return the linear index of the element in a multi-dimensional grid
/// The element is represented as a vector of coordinates in `dims`.
fn linearize_index(elem: &[usize], dims: &[usize]) -> usize {
    let mut index: usize = 0;
    for (d, c) in elem.iter().enumerate() {
        index += c * dims[0..d].iter().product::<usize>();
    }
    index
}

/// given a linear index of the element, return the vector of coordinates in a
/// multi-dimensional grid of `dims` dimensions.
fn delinearize_index(index: usize, dims: &[usize]) -> Vec<usize> {
    let mut idx = index;
    let mut elem = (0..dims.len()).map(|_| 0).collect::<Vec<usize>>();

    for (d, m) in dims.iter().enumerate().rev() {
        let prod = dims[0..d].iter().product::<usize>();
        if d == 0 {
            elem[d] = idx % m;
        } else {
            elem[d] = idx / prod;
            idx -= elem[d] * prod;
        }
    }
    elem
}

/// Aggregate to hold port properties for input and output links.
///
/// PortProperties are used throughout topology building functions, and are all
/// the same since our links are uniform.
struct PortConfiguration {
    incoming: PortProperties,
    outgoing: PortProperties,
}

impl PortConfiguration {
    // build port configurations based on the link configuration -- really only frame size.
    fn from_link_config(link_config: &LinkConfiguration) -> PortConfiguration {
        Self {
            incoming: PortProperties {
                direction: Direction::Incoming,
                frame_size: link_config.frame_size.into(),
                ..Default::default()
            },
            outgoing: PortProperties {
                direction: Direction::Outgoing,
                frame_size: link_config.frame_size.into(),
                ..Default::default()
            },
        }
    }
}

// check that the configurations to build the toologies were initialized without
// assigning the ports.
// the switch configuration is checked only if a configuration is passed.
fn validate_configurations(
    compute_config: &NodeConfiguration,
    switch_config: Option<&SwitchConfiguration>,
    _link_config: &LinkConfiguration,
) {
    assert_eq!(
        compute_config.num_inputs(),
        0,
        "compute node input links are configured by the topology"
    );
    assert_eq!(
        compute_config.num_outputs(),
        0,
        "compute node output links are configured by the topology"
    );
    if let Some(switch_config) = switch_config {
        assert_eq!(
            switch_config.input_link_count, 0,
            "switch input links are configured by the topology"
        );
        assert_eq!(
            switch_config.output_link_count, 0,
            "switch output links are configured by the topology"
        );
    }
}

#[cfg(test)]
mod topology_tests {
    use super::*;
    use itertools::Itertools;

    #[test]
    fn test_linearize() {
        assert_eq!(linearize_index(&[1, 1], &[4, 4]), 5);
        assert_eq!(linearize_index(&[1, 1], &[5, 5]), 6);
        assert_eq!(linearize_index(&[3, 3], &[4, 4]), 15);
    }
    #[test]
    fn test_delinearize() {
        assert_eq!(delinearize_index(6, &[4, 4]), vec![2, 1]);
        assert_eq!(delinearize_index(6, &[5, 5]), vec![1, 1]);
        assert_eq!(delinearize_index(15, &[4, 4]), vec![3, 3]);
    }
    #[test]
    fn test_lindelin() {
        let dims = vec![3, 4, 5, 6];
        for e in dims.iter().map(|&d| 0..d).multi_cartesian_product() {
            assert_eq!(delinearize_index(linearize_index(&e, &dims), &dims), e);
        }
    }
}
