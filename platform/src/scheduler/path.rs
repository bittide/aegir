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

use crate::error::Error;
use crate::hw::SwitchType;
use crate::specs::NodeSpec;
use crate::HardwareSpec;
use itertools::Itertools;
use petgraph::prelude::*;
use rand;
use rand::Rng;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;

// TODO(pouyad): applications can not currently send an output to multiple
// destinations. They're required to have one output per destination. This is a
// specification shortcoming in application semantics that needs addressing.

/// Paths are a prefix-tree (trie), with a single source and many possible
/// destinations. This is because switches can multicast data on route, which
/// allows a single source to drive many endpoints.
#[derive(Clone, Debug, Eq)]
pub struct Path {
    edge: EdgeIndex,
    terminal: bool,
    next_edge: Vec<Self>,
}

impl PartialEq for Path {
    fn eq(&self, other: &Self) -> bool {
        let eq_payload = self.edge == other.edge && self.terminal == other.terminal;
        if !eq_payload {
            return false;
        }
        if self.next_edge.len() != other.next_edge.len() {
            return false;
        }
        return eq_payload
            && self.next_edge.iter().all(|p_self| {
                other
                    .next_edge
                    .iter()
                    .find(|p_other| *p_other == p_self)
                    .is_some()
            });
    }
}

impl Path {
    pub fn new(path: &[EdgeIndex]) -> Result<Self, Error> {
        if path.len() == 0 || path.iter().collect::<HashSet<_>>().len() != path.len() {
            return Err(Error::InvalidPath);
        }
        let mut prefix = Self {
            edge: path[0],
            terminal: path.len() == 1,
            next_edge: vec![],
        };
        Self::add_path_rec(&mut prefix, 0, &path[1..]);
        Ok(prefix)
    }

    fn add_path_rec(&mut self, path_idx: usize, path: &[EdgeIndex]) {
        if path_idx == path.len() {
            return;
        }
        if let Some((prefix_idx, _)) = self
            .next_edge
            .iter()
            .find_position(|prefix| prefix.edge == path[path_idx])
        {
            Path::add_path_rec(&mut self.next_edge[prefix_idx], path_idx + 1, path);
        } else {
            let new_prefix = Path {
                edge: path[path_idx],
                terminal: path_idx + 1 == path.len(),
                next_edge: vec![],
            };
            self.next_edge.push(new_prefix);
            Path::add_path_rec(self.next_edge.last_mut().unwrap(), path_idx + 1, path);
        }
    }

    pub fn add_path(&mut self, path: &[EdgeIndex]) -> Result<(), Error> {
        // The first hop of any path to be added to the prefix tree must be the same.
        if path.len() == 0
            || path.iter().collect::<HashSet<_>>().len() != path.len()
            || path[0] != self.edge
        {
            return Err(Error::InvalidPath);
        }
        self.add_path_rec(1, &path);
        Ok(())
    }

    /// First-hop edge in the path.
    pub fn source(&self) -> EdgeIndex {
        self.edge
    }

    /// Returns a vector of last-hop edges in the path.
    pub fn destinations(&self) -> Vec<EdgeIndex> {
        fn destinations_rec(prefix: &Path, result: &mut Vec<EdgeIndex>) {
            if prefix.terminal {
                result.push(prefix.edge);
            }
            for next_prefix in &prefix.next_edge {
                destinations_rec(next_prefix, result);
            }
        }
        let mut destinations = vec![];
        destinations_rec(self, &mut destinations);
        destinations
    }

    /// Get all switch hops in a path, a switch hop is a tuple described by the
    /// ingress link and all corresponding egress links when a switch is
    /// traversed.
    pub fn switch_hops(&self) -> Vec<(EdgeIndex, Vec<EdgeIndex>)> {
        fn switch_hops_rec(prefix: &Path, result: &mut Vec<(EdgeIndex, Vec<EdgeIndex>)>) {
            if prefix.terminal {
                return;
            }
            if !prefix.next_edge.is_empty() {
                result.push((
                    prefix.edge,
                    prefix
                        .next_edge
                        .iter()
                        .map(|next_prefix| next_prefix.edge)
                        .collect::<Vec<_>>(),
                ));
            }
            for next_prefix in &prefix.next_edge {
                switch_hops_rec(next_prefix, result);
            }
        }
        let mut result = vec![];
        switch_hops_rec(self, &mut result);
        result
    }

    /// A mapping of link ids to the latency to which the link will receive the
    /// frame. The send time (tx) plus the latency is equal to the receive (rx)
    /// time.
    pub fn path_latencies(&self, sys_spec: &HardwareSpec) -> HashMap<EdgeIndex, i64> {
        fn arrival_times_rec(
            prefix: &Path,
            sys_spec: &HardwareSpec,
            result: &mut HashMap<EdgeIndex, i64>,
        ) {
            let ingress_rx_time = result[&prefix.edge];
            for next_prefix in &prefix.next_edge {
                let (src_node_id, _) = sys_spec.get_link_endpoints(next_prefix.edge);
                // The 1x1 mapping only supports switches with registered IO
                // interfaces. (No circular buffers.)
                assert_eq!(
                    sys_spec
                        .get_node(src_node_id)
                        .borrow()
                        .into_provisioned_switch_node()
                        .expect(
                            format!(
                                "link id {:?} should originate from a switch",
                                next_prefix.edge
                            )
                            .as_str()
                        )
                        .switch_type(),
                    SwitchType::Registered
                );
                let crossbar_latency = sys_spec
                    .get_node(src_node_id)
                    .borrow()
                    .into_provisioned_switch_node()
                    .unwrap()
                    .crossbar_latency()
                    .0 as i64;
                // A switch has a built in latency of 1, i.e., when the switch
                // node is stepped, data from its RX buffer is transferred to TX
                // buffer (when crossbar latency is 0).
                let egress_latency = sys_spec.ugn(next_prefix.edge);
                result.insert(
                    next_prefix.edge,
                    ingress_rx_time + 1 + crossbar_latency + egress_latency,
                );
                arrival_times_rec(next_prefix, sys_spec, result);
            }
        }
        let mut result = HashMap::new();
        result.insert(self.source(), sys_spec.ugn(self.source()));
        arrival_times_rec(self, sys_spec, &mut result);
        result
    }

    /// Returns all the links in the path as a vector; no ordering should be
    /// assumed in the result.
    pub fn all_links(&self) -> Vec<EdgeIndex> {
        fn all_links_rec(prefix: &Path, result: &mut Vec<EdgeIndex>) {
            result.push(prefix.edge);
            for next_prefix in &prefix.next_edge {
                all_links_rec(next_prefix, result);
            }
        }
        let mut result = vec![];
        all_links_rec(self, &mut result);
        result
    }
}

pub fn random_path(
    sys_spec: &HardwareSpec,
    src_node: NodeIndex,
    dst_node: &[NodeIndex],
) -> Result<Option<Path>, Error> {
    fn random_path_rec(
        sys_spec: &HardwareSpec,
        rng: &mut rand::rngs::ThreadRng,
        visited: &mut HashSet<NodeIndex>,
        src_node: NodeIndex,
        dst_node: &HashSet<NodeIndex>,
        current_path: &mut Vec<EdgeIndex>,
        accumulator: &mut Vec<Vec<EdgeIndex>>,
    ) {
        if dst_node.contains(&src_node) {
            accumulator.push(current_path.clone());
            return;
        }
        if visited.contains(&src_node) {
            return;
        }
        visited.insert(src_node);
        let mut out_edges = sys_spec
            .get_output_links(src_node)
            .map(|edge_ref| edge_ref.id())
            .collect::<Vec<_>>();
        while !out_edges.is_empty() {
            let out_edge_idx = rng.gen_range(0..out_edges.len());
            let out_edge = out_edges.swap_remove(out_edge_idx);
            current_path.push(out_edge);
            let (_, out_edge_dst) = sys_spec.get_link_endpoints(out_edge);
            random_path_rec(
                sys_spec,
                rng,
                visited,
                out_edge_dst,
                dst_node,
                current_path,
                accumulator,
            );
            current_path.pop();
        }
    }

    let mut rng = rand::thread_rng();
    let mut visited = HashSet::new();
    let mut current_path = vec![];
    let mut accumulator = vec![];
    let dst_nodes = HashSet::from_iter(dst_node.iter().cloned());
    if dst_nodes.contains(&src_node) {
        return Err(Error::InvalidPath);
    }
    random_path_rec(
        sys_spec,
        &mut rng,
        &mut visited,
        src_node,
        &dst_nodes,
        &mut current_path,
        &mut accumulator,
    );
    if accumulator.is_empty() {
        return Ok(None);
    }
    let mut path = Path::new(accumulator[0].as_slice())?;
    for a_path in accumulator.iter().skip(1) {
        path.add_path(a_path.as_slice())?;
    }
    Ok(Some(path))
}

#[cfg(test)]
mod path_tests {
    use crate::error::Error;
    use crate::hw::config::SwitchConfiguration;
    use crate::hw::topologies::fat_tree;
    use crate::scheduler::path::Path;
    use crate::specs::NodeSpec;
    use crate::HardwareSpec;
    use crate::LinkConfiguration;
    use crate::NodeConfiguration;
    use petgraph::prelude::*;
    use std::collections::HashMap;
    use std::collections::HashSet;

    use super::random_path;

    #[allow(dead_code)]
    struct TestSysSpec {
        sys_spec: HardwareSpec,
        compute0: NodeIndex,
        compute1: NodeIndex,
        compute2: NodeIndex,
        compute3: NodeIndex,
        switch01: NodeIndex,
        switch02: NodeIndex,
        switch11: NodeIndex,
        link_compute0_switch01: EdgeIndex,
        link_compute1_switch01: EdgeIndex,
        link_switch01_switch02: EdgeIndex,
        link_switch02_switch11: EdgeIndex,
        link_switch11_compute2: EdgeIndex,
        link_switch11_compute3: EdgeIndex,
        link_switch01_compute1: EdgeIndex,
    }

    fn build_sys_spec() -> TestSysSpec {
        let sys_spec = fat_tree(
            3,
            &NodeConfiguration::default(),
            &SwitchConfiguration {
                crossbar_latency: 3,
                ..Default::default()
            },
            &LinkConfiguration {
                latency: 3,
                ..Default::default()
            },
        );
        fn first_edge_to_dst(sys_spec: &HardwareSpec, src: NodeIndex, dst: NodeIndex) -> EdgeIndex {
            sys_spec
                .get_output_links(src)
                .find(|edge_ref| sys_spec.get_link_endpoints(edge_ref.id()).1 == dst)
                .map(|edge_ref| edge_ref.id())
                .unwrap()
        }
        let compute0 = sys_spec.get_node_index_by_name("compute_0").unwrap();
        let compute1 = sys_spec.get_node_index_by_name("compute_1").unwrap();
        let compute2 = sys_spec.get_node_index_by_name("compute_2").unwrap();
        let compute3 = sys_spec.get_node_index_by_name("compute_3").unwrap();
        let switch01 = sys_spec.get_node_index_by_name("switch_0_1").unwrap();
        let switch02 = sys_spec.get_node_index_by_name("switch_0_2").unwrap();
        let switch11 = sys_spec.get_node_index_by_name("switch_1_1").unwrap();
        let link_compute0_switch01 = first_edge_to_dst(&sys_spec, compute0, switch01);
        let link_compute1_switch01 = first_edge_to_dst(&sys_spec, compute1, switch01);
        let link_switch01_switch02 = first_edge_to_dst(&sys_spec, switch01, switch02);
        let link_switch02_switch11 = first_edge_to_dst(&sys_spec, switch02, switch11);
        let link_switch11_compute2 = first_edge_to_dst(&sys_spec, switch11, compute2);
        let link_switch11_compute3 = first_edge_to_dst(&sys_spec, switch11, compute3);
        let link_switch01_compute1 = first_edge_to_dst(&sys_spec, switch01, compute1);
        TestSysSpec {
            sys_spec: sys_spec,
            compute0,
            compute1,
            compute2,
            compute3,
            switch01,
            switch02,
            switch11,
            link_compute0_switch01,
            link_switch01_switch02,
            link_switch02_switch11,
            link_switch11_compute2,
            link_compute1_switch01,
            link_switch11_compute3,
            link_switch01_compute1,
        }
    }

    #[test]
    fn test_new_empty_path() {
        let result = Path::new([].as_slice());
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), Error::InvalidPath);
    }

    #[test]
    fn test_new() {
        let ts = build_sys_spec();
        let first_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        //     compute0
        //         |
        //      switch01
        //         |
        //      switch02
        //         |
        //      switch11
        //         |
        //      compute2
        let path = Path::new(first_path.as_slice()).unwrap();
        assert_eq!(path.edge, ts.link_compute0_switch01);
        assert_eq!(path.terminal, false);
        assert_eq!(path.next_edge.len(), 1);
        let prefix = &path.next_edge[0];
        assert_eq!(prefix.edge, ts.link_switch01_switch02);
        assert_eq!(prefix.terminal, false);
        assert_eq!(prefix.next_edge.len(), 1);
        let prefix = &prefix.next_edge[0];
        assert_eq!(prefix.edge, ts.link_switch02_switch11);
        assert_eq!(prefix.terminal, false);
        assert_eq!(prefix.next_edge.len(), 1);
        let prefix = &prefix.next_edge[0];
        assert_eq!(prefix.edge, ts.link_switch11_compute2);
        assert_eq!(prefix.terminal, true);
    }

    #[test]
    fn test_union_update_empty_path() {
        let ts = build_sys_spec();
        let first_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        let mut path = Path::new(first_path.as_slice()).unwrap();
        assert_eq!(
            path.add_path([].as_slice()).unwrap_err(),
            Error::InvalidPath
        );
    }

    #[test]
    fn test_union_update_non_prefix_path() {
        let ts = build_sys_spec();
        let first_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        let mut path = Path::new(first_path.as_slice()).unwrap();
        let second_path = [
            ts.link_compute1_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        assert_eq!(
            path.add_path(second_path.as_slice()).unwrap_err(),
            Error::InvalidPath
        );
    }

    #[test]
    fn test_union_update_prefix_path() {
        let ts = build_sys_spec();
        let first_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        let mut path = Path::new(first_path.as_slice()).unwrap();
        let second_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute3,
        ];
        assert!(path.add_path(second_path.as_slice()).is_ok());

        //     compute0
        //         |
        //      switch01
        //         |
        //      switch02
        //         |
        //      switch11 ---- compute3
        //         |
        //      compute2
        assert_eq!(path.edge, ts.link_compute0_switch01);
        assert_eq!(path.terminal, false);
        assert_eq!(path.next_edge.len(), 1);
        let prefix = &path.next_edge[0];
        assert_eq!(prefix.edge, ts.link_switch01_switch02);
        assert_eq!(prefix.terminal, false);
        assert_eq!(prefix.next_edge.len(), 1);
        let prefix = &prefix.next_edge[0];
        assert_eq!(prefix.edge, ts.link_switch02_switch11);
        assert_eq!(prefix.terminal, false);
        assert_eq!(prefix.next_edge.len(), 2);
        let prefix0 = &prefix.next_edge[0];
        assert_eq!(prefix0.edge, ts.link_switch11_compute2);
        assert_eq!(prefix0.terminal, true);
        let prefix1 = &prefix.next_edge[1];
        assert_eq!(prefix1.edge, ts.link_switch11_compute3);
        assert_eq!(prefix1.terminal, true);
    }

    #[test]
    fn test_union_update_2_prefix_paths() {
        let ts = build_sys_spec();
        let first_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        let mut path = Path::new(first_path.as_slice()).unwrap();
        let second_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute3,
        ];
        assert!(path.add_path(second_path.as_slice()).is_ok());

        let third_path = [ts.link_compute0_switch01, ts.link_switch01_compute1];
        assert!(path.add_path(third_path.as_slice()).is_ok());

        //     compute0
        //         |
        //      switch01 ------ switch02
        //         |               |
        //      compute1        switch11 ---- compute3
        //                         |
        //                      compute2
        assert_eq!(path.edge, ts.link_compute0_switch01);
        assert_eq!(path.terminal, false);

        assert_eq!(path.next_edge.len(), 2);
        let prefix0 = &path.next_edge[0];
        assert_eq!(prefix0.edge, ts.link_switch01_switch02);
        assert_eq!(prefix0.terminal, false);
        let prefix1 = &path.next_edge[1];
        assert_eq!(prefix1.edge, ts.link_switch01_compute1);
        assert_eq!(prefix1.terminal, true);

        assert_eq!(prefix0.next_edge.len(), 1);
        let prefix = &prefix0.next_edge[0];
        assert_eq!(prefix.edge, ts.link_switch02_switch11);
        assert_eq!(prefix.terminal, false);

        assert_eq!(prefix.next_edge.len(), 2);
        let prefix0 = &prefix.next_edge[0];
        assert_eq!(prefix0.edge, ts.link_switch11_compute2);
        assert_eq!(prefix0.terminal, true);
        let prefix1 = &prefix.next_edge[1];
        assert_eq!(prefix1.edge, ts.link_switch11_compute3);
        assert_eq!(prefix1.terminal, true);

        assert_eq!(path.source(), ts.link_compute0_switch01);
        assert_eq!(
            path.destinations().iter().collect::<HashSet<_>>(),
            HashSet::from([
                &ts.link_switch01_compute1,
                &ts.link_switch11_compute2,
                &ts.link_switch11_compute3
            ])
        )
    }

    #[test]
    fn test_switch_hops() {
        let ts = build_sys_spec();
        let first_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        let mut path = Path::new(first_path.as_slice()).unwrap();
        let second_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute3,
        ];
        assert!(path.add_path(second_path.as_slice()).is_ok());
        let third_path = [ts.link_compute0_switch01, ts.link_switch01_compute1];
        assert!(path.add_path(third_path.as_slice()).is_ok());

        let switch_hops = path.switch_hops();
        assert!(switch_hops
            .iter()
            .find(|(ingress, egress)| {
                (ingress, egress)
                    == (
                        &ts.link_compute0_switch01,
                        &vec![ts.link_switch01_switch02, ts.link_switch01_compute1],
                    )
            })
            .is_some());
        assert!(switch_hops
            .iter()
            .find(|(ingress, egress)| {
                (ingress, egress) == (&ts.link_switch01_switch02, &vec![ts.link_switch02_switch11])
            })
            .is_some());
        assert!(switch_hops
            .iter()
            .find(|(ingress, egress)| {
                (ingress, egress)
                    == (
                        &ts.link_switch02_switch11,
                        &vec![ts.link_switch11_compute2, ts.link_switch11_compute3],
                    )
            })
            .is_some());
        assert_eq!(switch_hops.len(), 3);
    }

    #[test]
    fn test_all_links() {
        let ts = build_sys_spec();
        let first_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ];
        let mut path = Path::new(first_path.as_slice()).unwrap();
        let second_path = [
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute3,
        ];
        assert!(path.add_path(second_path.as_slice()).is_ok());
        let third_path = [ts.link_compute0_switch01, ts.link_switch01_compute1];
        assert!(path.add_path(third_path.as_slice()).is_ok());

        assert_eq!(
            path.all_links().iter().collect::<HashSet<_>>(),
            HashSet::from([
                &ts.link_compute0_switch01,
                &ts.link_switch01_switch02,
                &ts.link_switch02_switch11,
                &ts.link_switch11_compute2,
                &ts.link_switch11_compute3,
                &ts.link_switch01_compute1,
            ])
        )
    }

    #[test]
    fn test_random_path() {
        let ts = build_sys_spec();
        let destinations = [ts.compute2, ts.compute3];
        let path = random_path(&ts.sys_spec, ts.compute0, &destinations)
            .unwrap()
            .unwrap();
        assert_eq!(path.source(), ts.link_compute0_switch01);
        assert_eq!(
            path.destinations().iter().collect::<HashSet<_>>(),
            HashSet::from([&ts.link_switch11_compute2, &ts.link_switch11_compute3])
        );
        let path_hops = path.switch_hops().drain(..).collect::<HashMap<_, _>>();

        fn reaches(
            edge: &EdgeIndex,
            path_hops: &HashMap<EdgeIndex, Vec<EdgeIndex>>,
            sys_spec: &HardwareSpec,
            destinations: &[NodeIndex],
            found: &mut Vec<NodeIndex>,
        ) {
            if !path_hops.contains_key(&edge) {
                let (_, dst) = sys_spec.get_link_endpoints(*edge);
                if destinations
                    .iter()
                    .find(|node_id| **node_id == dst)
                    .is_some()
                {
                    found.push(dst);
                }
            } else {
                for next_edge in &path_hops[edge] {
                    reaches(next_edge, path_hops, sys_spec, destinations, found);
                }
            }
        }
        let mut found_dst = vec![];
        reaches(
            &path.source(),
            &path_hops,
            &ts.sys_spec,
            &destinations,
            &mut found_dst,
        );
        assert_eq!(
            found_dst.drain(..).collect::<HashSet<_>>(),
            HashSet::from(destinations)
        );
    }

    #[test]
    fn test_path_latencies() {
        let ts = build_sys_spec();
        let path = Path::new(&[
            ts.link_compute0_switch01,
            ts.link_switch01_switch02,
            ts.link_switch02_switch11,
            ts.link_switch11_compute2,
        ])
        .unwrap();
        assert_eq!(path.source(), ts.link_compute0_switch01);
        assert_eq!(path.destinations(), vec![ts.link_switch11_compute2]);

        assert!(ts
            .sys_spec
            .iter_nodes()
            .filter(|node_id| ts
                .sys_spec
                .get_node(*node_id)
                .borrow()
                .into_provisioned_switch_node()
                .is_some())
            .all(|node_id| ts
                .sys_spec
                .get_node(node_id)
                .borrow()
                .into_provisioned_switch_node()
                .unwrap()
                .crossbar_latency()
                .0
                == 3));
        assert_eq!(
            path.path_latencies(&ts.sys_spec),
            HashMap::from([
                (
                    ts.link_compute0_switch01,
                    ts.sys_spec.ugn(ts.link_compute0_switch01),
                ),
                (
                    ts.link_switch01_switch02,
                    ts.sys_spec.ugn(ts.link_compute0_switch01)
                        + 3
                        + 1
                        + ts.sys_spec.ugn(ts.link_switch01_switch02),
                ),
                (
                    ts.link_switch02_switch11,
                    ts.sys_spec.ugn(ts.link_compute0_switch01)
                        + 3
                        + 1
                        + ts.sys_spec.ugn(ts.link_switch01_switch02)
                        + 3
                        + 1
                        + ts.sys_spec.ugn(ts.link_switch02_switch11),
                ),
                (
                    ts.link_switch11_compute2,
                    ts.sys_spec.ugn(ts.link_compute0_switch01)
                        + 3
                        + 1
                        + ts.sys_spec.ugn(ts.link_switch01_switch02)
                        + 3
                        + 1
                        + ts.sys_spec.ugn(ts.link_switch02_switch11)
                        + 3
                        + 1
                        + ts.sys_spec.ugn(ts.link_switch11_compute2)
                )
            ])
        )
    }
}
