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

use crate::app::ServiceHandle;
use crate::calendar::Calendar;
use crate::calendar::CalendarEntry;
use crate::calendar::CalendarSpec;
use crate::calendar::CrossbarCalendar;
use crate::calendar::CrossbarCalendarEntry;
use crate::calendar::NodeCalendar;
use crate::calendar::NodeCalendarEntry;
use crate::error::Error;
use crate::hw::SwitchType;
use crate::mailbox;
use crate::scheduler::path::Path;
use crate::scheduler::SystemAllocation;
use crate::Application;
use crate::Buffering;
use crate::Cycle;
use crate::HardwareSpec;
use crate::NodeSpec;
use crate::BUFFERING_DOUBLE;
use crate::BUFFERING_SINGLE;
use petgraph::prelude::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;

use super::alloc::compute_batch_size;
use super::alloc::PathBatching;

#[derive(Clone, Debug, PartialEq, Eq)]
struct PathIndex(usize);

impl PathIndex {
    pub fn new(value: usize) -> Self {
        Self(value)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommsAttrs {
    address: usize,
    path_idx: PathIndex,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunAttrs {
    service_handle: ServiceHandle,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SwitchReservation {
    muxes: HashMap<EdgeIndex, Vec<EdgeIndex>>,
    path_idx: PathIndex,
}

impl SwitchReservation {
    fn conflicts(&self, other: &SwitchReservation) -> bool {
        !self
            .muxes
            .keys()
            .collect::<HashSet<_>>()
            .is_disjoint(&other.muxes.keys().collect::<HashSet<_>>())
            || !self
                .muxes
                .values()
                .flatten()
                .collect::<HashSet<_>>()
                .is_disjoint(&other.muxes.values().flatten().collect::<HashSet<_>>())
    }

    /// Merge the `other` switch reservation into `self`.
    fn merge(&mut self, other: &SwitchReservation) -> Result<(), Error> {
        if self.conflicts(other) {
            return Err(Error::InvalidAllocation);
        }
        self.muxes.extend(other.muxes.clone().drain());
        Ok(())
    }

    /// Get the crossbar calendar entry for the switch reservation.
    pub fn calendar_entry(&self, sys_spec: &HardwareSpec) -> CrossbarCalendarEntry {
        if self.muxes.is_empty() {
            return CrossbarCalendarEntry {
                input_source: None,
                frame_count: 1,
            };
        }
        let (_, switch_node_id) = sys_spec.get_link_endpoints(*self.muxes.keys().next().unwrap());
        assert!(sys_spec
            .get_node(switch_node_id)
            .borrow()
            .into_provisioned_switch_node()
            .is_some());
        let output_count = sys_spec.get_output_links(switch_node_id).count() as u32;
        let mut mux = (0..output_count).collect::<Vec<_>>();
        for (ingress, egress_edges) in self.muxes.iter() {
            assert_eq!(sys_spec.get_link_endpoints(*ingress).1, switch_node_id);
            let ingress_port: usize = sys_spec.get_link(*ingress).dst_port().into();
            for egress in egress_edges {
                assert_eq!(sys_spec.get_link_endpoints(*egress).0, switch_node_id);
                let egress_port: usize = sys_spec.get_link(*egress).src_port().into();
                mux[egress_port] = ingress_port as u32;
            }
        }
        CrossbarCalendarEntry {
            input_source: Some(mux),
            frame_count: 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NodeAction {
    Switch(SwitchReservation),
    Compute(RunAttrs),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkAction {
    gather: Option<CommsAttrs>,
    scatter: Option<CommsAttrs>,
}

impl LinkAction {
    /// Two link actions conflict if their gather/scatter endpoints are both in use.
    fn conflicts(&self, other: &LinkAction) -> bool {
        if self.gather.is_some() && other.gather.is_some() {
            return true;
        }
        if self.scatter.is_some() && other.scatter.is_some() {
            return true;
        }
        false
    }

    fn merge(&mut self, other: &LinkAction) -> Result<(), Error> {
        if self.conflicts(other) {
            return Err(Error::InvalidAllocation);
        }
        if self.gather.is_none() {
            self.gather = other.gather.clone();
        }
        if self.scatter.is_none() {
            self.scatter = other.scatter.clone();
        }
        Ok(())
    }
}

impl NodeAction {
    fn conflicts(&self, other: &NodeAction) -> bool {
        match (self, other) {
            (NodeAction::Switch(rsv), NodeAction::Switch(other_rsv)) => rsv.conflicts(other_rsv),
            (NodeAction::Compute(_), NodeAction::Compute(_)) => true,
            (_, _) => panic!("disjoint actions"),
        }
    }

    /// Merge `self` with `other`, with the assertions that they're conflict
    /// free and merge-able.
    fn merge(&mut self, other: &NodeAction) -> Result<(), Error> {
        if self.conflicts(other) {
            return Err(Error::InvalidAllocation);
        }
        match (self, other) {
            (NodeAction::Switch(rsv), NodeAction::Switch(other_rsv)) => rsv.merge(other_rsv),
            (_, _) => Err(Error::InvalidAllocation),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReservationTable {
    pub node_table: HashMap<NodeIndex, HashMap<Cycle, NodeAction>>,
    pub link_table: HashMap<EdgeIndex, HashMap<Cycle, LinkAction>>,
    pub paths: Vec<Path>,
    pub batching: Vec<PathBatching>,
}

impl ReservationTable {
    fn new() -> Self {
        Self {
            node_table: HashMap::new(),
            link_table: HashMap::new(),
            paths: vec![],
            batching: vec![],
        }
    }

    // Creates an empty (no cycles) reservation table hosting the specified nodes.
    fn new_for_resources(node_ids: &[NodeIndex], link_ids: &[EdgeIndex]) -> Self {
        Self {
            node_table: HashMap::from_iter(
                node_ids.iter().map(|node_id| (*node_id, HashMap::new())),
            ),
            link_table: HashMap::from_iter(
                link_ids.iter().map(|link_id| (*link_id, HashMap::new())),
            ),
            paths: vec![],
            batching: vec![],
        }
    }

    /// Determines if this reservation table and `other_table` are conflict free
    /// when `other_table` is offset by `offset`.
    fn conflicts(&self, other: &Self, offset: usize) -> bool {
        if other.batching.len() > 1 {
            unimplemented!("Offsetting multiple paths together is unimplemented.");
        }
        for sys_node in self.common_nodes(other) {
            let self_node_table = &self.node_table[&sys_node];
            let other_node_table = &other.node_table[&sys_node];
            for (other_cycle, other_action) in other_node_table.iter() {
                match other_action {
                    NodeAction::Switch(_) => {
                        assert_eq!(other.batching.len(), 1);
                        let effective_cycle = other_cycle + offset;
                        if let Some(self_action) = self_node_table.get(&effective_cycle) {
                            if other_action.conflicts(self_action) {
                                return true;
                            }
                        }
                    }
                    NodeAction::Compute(_) => {
                        let effective_cycle = other_cycle + offset;
                        if let Some(self_action) = self_node_table.get(&effective_cycle) {
                            if other_action.conflicts(&self_action) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        for link_id in self.common_links(other) {
            let self_link_table = &self.link_table[&link_id];
            let other_link_table = &other.link_table[&link_id];
            for (other_cycle, other_action) in other_link_table.iter() {
                let effective_cycle = other_cycle + offset;
                if let Some(self_action) = self_link_table.get(&effective_cycle) {
                    if other_action.conflicts(self_action) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    fn new_compute_reservation(
        sys_spec: &HardwareSpec,
        alloc: &SystemAllocation,
        app_node: &ServiceHandle,
    ) -> Self {
        assert!(alloc.nodes.contains_key(&app_node));
        let sys_node = alloc.nodes[&app_node];
        let app_cycles = alloc.compute_cycles[&app_node];
        let mut rsv = ReservationTable::new_for_resources(&[sys_node], &[]);
        let sys_node_starting_cycles = sys_spec
            .get_node(sys_node)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        for i in 0..app_cycles {
            rsv.node_table.get_mut(&sys_node).unwrap().insert(
                sys_node_starting_cycles + i,
                NodeAction::Compute(RunAttrs {
                    service_handle: app_node.clone(),
                }),
            );
        }
        rsv
    }

    fn new_comms_reservation(
        sys_spec: &HardwareSpec,
        alloc: &SystemAllocation,
        outboxes: &[&mailbox::ConnectionAttrs],
    ) -> Self {
        // TODO(pouyad): batch outboxes with the same path.
        assert!(outboxes.len() == 1);
        let outbox = outboxes[0];
        let app_edge_id = outbox.connection_id.clone();
        let path = &alloc.links[&app_edge_id];
        if path.is_none() {
            // TODO(pouyad) Model host memory I/O limitations; no free lunch.
            return ReservationTable::new();
        }
        let path = path.as_ref().unwrap();
        let batching = compute_batch_size(sys_spec, &path);
        let frame_size = outbox.mapped_endpoint.as_ref().unwrap().frame_size;
        let frame_count =
            outbox.message_size / frame_size + usize::from(outbox.message_size % frame_size != 0);
        let (src_node_id, _) = sys_spec.get_link_endpoints(path.source());
        let src_start_time = sys_spec
            .get_node(src_node_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        let rsv_nodes: Vec<NodeIndex> = path
            .switch_hops()
            .iter()
            .map(|(link_id, _)| {
                let (_, switch_id) = sys_spec.get_link_endpoints(*link_id);
                switch_id
            })
            .collect::<Vec<_>>();
        let mut rsv = ReservationTable::new_for_resources(
            &rsv_nodes.as_slice(),
            &path.all_links().as_slice(),
        );
        let latencies = path.path_latencies(sys_spec);
        rsv.paths.push(path.clone());
        rsv.batching.push(batching.clone());

        // Source markings
        let src_base_address = outbox
            .mapped_endpoint
            .as_ref()
            .unwrap()
            .base_address
            .expect("Addresses must be materialized.");
        for k in 0..frame_count {
            let cycle = src_start_time + k;
            assert!(!rsv.link_table[&path.source()].contains_key(&cycle));
            rsv.link_table.get_mut(&path.source()).unwrap().insert(
                cycle,
                LinkAction {
                    gather: Some(CommsAttrs {
                        address: src_base_address + k,
                        path_idx: PathIndex::new(0),
                    }),
                    scatter: None,
                },
            );
        }
        // Destination markings.
        for dst_edge_id in path.destinations() {
            let latency = latencies[&dst_edge_id];
            let (_, dst_node_id) = sys_spec.get_link_endpoints(dst_edge_id);
            let dst_start_time = sys_spec
                .get_node(dst_node_id)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .starting_cycles();
            let arrival_time = (src_start_time as i64 + latency) as usize;
            assert!(arrival_time > dst_start_time);
            // let delay_from_start = arrival_time - dst_start_time;
            let dst_base_address = sys_spec
                .get_node(dst_node_id)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .get_mailbox()
                .unwrap()
                .inboxes
                .iter()
                .find(|inbox| inbox.connection_id == app_edge_id)
                .unwrap()
                .mapped_endpoint
                .as_ref()
                .unwrap()
                .base_address
                .unwrap();
            for k in 0..frame_count {
                let cycle = arrival_time + k;
                assert!(!rsv.link_table[&dst_edge_id].contains_key(&cycle));
                rsv.link_table.get_mut(&dst_edge_id).unwrap().insert(
                    cycle,
                    LinkAction {
                        gather: None,
                        scatter: Some(CommsAttrs {
                            address: dst_base_address + k,
                            path_idx: PathIndex::new(0),
                        }),
                    },
                );
            }
        }
        // Switch+Link markings en route.
        for (ingress, egress) in path.switch_hops() {
            let (_, switch_node_id) = sys_spec.get_link_endpoints(ingress);
            let ingress_latency = latencies[&ingress];
            let switch_starting_cycle = sys_spec
                .get_node(switch_node_id)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .starting_cycles();
            let switch_rx_cycle = (src_start_time as i64 + ingress_latency) as usize;
            let crossbar_latency = sys_spec
                .get_node(switch_node_id)
                .borrow()
                .into_provisioned_switch_node()
                .unwrap()
                .crossbar_latency()
                .0;
            assert_eq!(
                sys_spec
                    .get_node(switch_node_id)
                    .borrow()
                    .into_provisioned_switch_node()
                    .unwrap()
                    .switch_type(),
                SwitchType::Registered
            );
            assert!((switch_rx_cycle + crossbar_latency) >= switch_starting_cycle);
            for k in 0..frame_count {
                let cycle = switch_rx_cycle + crossbar_latency + k;
                assert!(!rsv.node_table[&switch_node_id].contains_key(&cycle));
                rsv.node_table.get_mut(&switch_node_id).unwrap().insert(
                    cycle,
                    NodeAction::Switch(SwitchReservation {
                        muxes: HashMap::from([(ingress, egress.clone())]),
                        path_idx: PathIndex::new(0),
                    }),
                );
                let cycle = switch_rx_cycle + k;
                let ingress_action = LinkAction {
                    scatter: Some(CommsAttrs {
                        address: 0,
                        path_idx: PathIndex::new(0),
                    }),
                    gather: None,
                };
                // The link may already have a cycle reservation, e.g., if UGN was zero.
                if rsv.link_table[&ingress].contains_key(&cycle) {
                    rsv.link_table
                        .get_mut(&ingress)
                        .unwrap()
                        .get_mut(&cycle)
                        .map(|link_action| link_action.merge(&ingress_action).unwrap());
                } else {
                    rsv.link_table
                        .get_mut(&ingress)
                        .unwrap()
                        .insert(cycle, ingress_action);
                }
                for edge in &egress {
                    let cycle = switch_rx_cycle + crossbar_latency + 1 + k;
                    let egress_action = LinkAction {
                        scatter: None,
                        gather: Some(CommsAttrs {
                            address: 0,
                            path_idx: PathIndex::new(0),
                        }),
                    };
                    if rsv.link_table[&edge].contains_key(&cycle) {
                        rsv.link_table
                            .get_mut(&edge)
                            .unwrap()
                            .get_mut(&cycle)
                            .map(|link_action| {
                                link_action.merge(&egress_action).unwrap();
                            });
                    } else {
                        rsv.link_table
                            .get_mut(&edge)
                            .unwrap()
                            .insert(cycle, egress_action);
                    }
                }
            }
        }
        rsv
    }

    /// Returns reservations for all processing implied by the allocation; this is
    /// currently a tuple (compute, communication), which are reservations for computation
    /// and communication respectively.
    fn new_reservations(
        app_spec: &Application,
        sys_spec: &HardwareSpec,
        alloc: &SystemAllocation,
    ) -> (Vec<ReservationTable>, Vec<ReservationTable>) {
        // Computation: every service assigned to a compute node needs to run.
        let compute_reservations = app_spec
            .iter_nodes()
            .map(|app_node_id| {
                Self::new_compute_reservation(
                    sys_spec,
                    alloc,
                    &ServiceHandle::new(app_spec.id(), app_node_id),
                )
            })
            .collect::<Vec<_>>();
        // Communication: every outbox needs to have its contents transmitted to
        // the corresponding inboxes.
        // TODO(pouyad) multiple outboxes with the same path can be batched.
        let comms_reservations = sys_spec
            .compute_nodes()
            .iter()
            .flat_map(|sys_node_id| {
                sys_spec
                    .get_node(*sys_node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .get_mailbox()
                    .map_or(vec![], |mailbox| {
                        mailbox
                            .outboxes
                            .iter()
                            .map(|outbox| Self::new_comms_reservation(sys_spec, alloc, &[outbox]))
                            .collect::<Vec<_>>()
                    })
            })
            .collect::<Vec<_>>();
        (compute_reservations, comms_reservations)
    }

    /// Common nodes between `self` and `other`. These are the nodes of interest
    /// when considering two reservation tables since they're the ones with
    /// possible contention.
    fn common_nodes(&self, other: &ReservationTable) -> HashSet<NodeIndex> {
        self.node_table
            .iter()
            .map(|(k, v)| {
                assert!(!v.is_empty());
                k
            })
            .collect::<HashSet<_>>()
            .intersection(
                &other
                    .node_table
                    .iter()
                    .map(|(k, v)| {
                        assert!(!v.is_empty());
                        k
                    })
                    .collect::<HashSet<_>>(),
            )
            .map(|x| **x)
            .collect()
    }

    /// Common links between `self` and `other`. May conflict when merging.
    fn common_links(&self, other: &ReservationTable) -> HashSet<EdgeIndex> {
        self.link_table
            .iter()
            .map(|(k, v)| {
                assert!(!v.is_empty());
                k
            })
            .collect::<HashSet<_>>()
            .intersection(
                &other
                    .link_table
                    .iter()
                    .map(|(k, v)| {
                        assert!(!v.is_empty());
                        k
                    })
                    .collect::<HashSet<_>>(),
            )
            .map(|x| **x)
            .collect()
    }

    /// Checks that self is a simple (non-composite reservation table). A
    /// composite reservation table consists of more than one simple
    /// reservation, or other composite reservations. Simple reservation
    /// tables can be for
    ///
    /// 1. running a single service via NodeAction::Compute, or
    /// 2. Routing a single path
    fn is_simple_reservation(&self, sys_spec: &HardwareSpec) -> bool {
        let node_frequencies = self
            .node_table
            .keys()
            .map(|node_id| {
                sys_spec
                    .get_node(*node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .frequency()
                    .value
            })
            .collect::<HashSet<_>>();
        let link_frequencies = self
            .link_table
            .keys()
            .map(|link_id| {
                sys_spec
                    .get_link(*link_id)
                    .into_provisioned_link()
                    .unwrap()
                    .frequency()
                    .value
            })
            .collect::<HashSet<_>>();
        if self.paths.len() == 0 {
            // If there are no paths routed, then it must be a run action for a
            // single node.
            assert_eq!(self.batching.len(), 0);
            if !self.link_table.is_empty() {
                return false;
            }
            // There's a single compute node.
            return self.node_table.keys().count() == 1;
        } else if self.paths.len() == 1 {
            assert_eq!(self.batching.len(), 1);
            // All links and switches for the paths operate at the same frequency.
            return node_frequencies.union(&link_frequencies).count() == 1;
        }
        false
    }

    /// Merge `other` to `self` at the specified offset.
    fn merge(&mut self, other: &ReservationTable, offset: usize) -> Result<&mut Self, Error> {
        if self.conflicts(other, offset) {
            return Err(Error::InvalidMergeOffset);
        }
        for (node_id, other_node_cycles) in &other.node_table {
            let mut other_node_cycles = other_node_cycles
                .iter()
                .map(|(cycle, action)| {
                    let new_action = match action {
                        NodeAction::Switch(switch_rsv) => NodeAction::Switch(SwitchReservation {
                            path_idx: PathIndex::new(self.paths.len()),
                            ..switch_rsv.clone()
                        }),
                        _ => action.clone(),
                    };
                    (*cycle + offset, new_action)
                })
                .collect::<HashMap<_, _>>();
            let self_node_cycles = self.node_table.get_mut(node_id);
            if let Some(self_node_cycles) = self_node_cycles {
                for (cycle, other_action) in other_node_cycles.drain() {
                    let cycle_action = self_node_cycles.get_mut(&cycle);
                    if let Some(cycle_action) = cycle_action {
                        cycle_action.merge(&other_action)?;
                    } else {
                        self_node_cycles.insert(cycle, other_action);
                    }
                }
            } else {
                self.node_table.insert(*node_id, other_node_cycles);
            }
        }
        for (link_id, other_link_cycles) in &other.link_table {
            let mut other_link_cycles = other_link_cycles
                .iter()
                .map(|(cycle, action)| {
                    let mut new_action = action.clone();
                    if let Some(gather) = &mut new_action.gather {
                        gather.path_idx = PathIndex::new(self.paths.len());
                    }
                    if let Some(scatter) = &mut new_action.scatter {
                        scatter.path_idx = PathIndex::new(self.paths.len());
                    }
                    (*cycle + offset, new_action)
                })
                .collect::<HashMap<_, _>>();
            let self_link_cycles = self.link_table.get_mut(link_id);
            if let Some(self_link_cycles) = self_link_cycles {
                for (cycle, other_action) in other_link_cycles.drain() {
                    let cycle_action = self_link_cycles.get_mut(&cycle);
                    if let Some(cycle_action) = cycle_action {
                        cycle_action.merge(&other_action)?;
                    } else {
                        self_link_cycles.insert(cycle, other_action.clone());
                    }
                }
            } else {
                self.link_table.insert(*link_id, other_link_cycles);
            }
        }
        assert!(other.paths.len() <= 1);
        assert_eq!(other.batching.len(), other.paths.len());
        if other.paths.len() == 1 {
            self.paths.push(other.paths[0].clone());
            self.batching.push(other.batching[0].clone());
        }
        Ok(self)
    }

    /// Concatenate `other` to `self`.
    fn concat(
        &mut self,
        other: &ReservationTable,
        sys_spec: &HardwareSpec,
    ) -> Result<&mut Self, Error> {
        let common_nodes = self.common_nodes(other).drain().collect::<Vec<_>>();
        let common_links = self.common_links(other).drain().collect::<Vec<_>>();

        if common_nodes.is_empty() && common_links.is_empty() {
            // Without common nodes, `other` can be merged to self without conflicts.
            self.merge(other, 0)?;
            return Ok(self);
        }
        // TODO(pouyad): offsetting a mixture of actions isn't yet supported.
        // Here we assert that `other` is either: 1. computation for a single
        // node, 2. communication for a single path.
        assert!(other.is_simple_reservation(sys_spec));
        // Because all resources in `other` operate at the same frequencies,
        // then the common nodes between `self` and `other` also operate at the
        // same frequency.
        let frequencies = common_nodes
            .iter()
            .map(|node_id| {
                sys_spec
                    .get_node(*node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .frequency()
                    .value
            })
            .chain(common_links.iter().map(|link_id| {
                sys_spec
                    .get_link(*link_id)
                    .into_provisioned_link()
                    .unwrap()
                    .frequency()
                    .value
            }))
            .collect::<HashSet<_>>();
        assert_eq!(frequencies.len(), 1);
        // Index of resource whose schedule stretches out furthest in `self`.
        let max_node_busy = common_nodes
            .iter()
            .map(|node_id| {
                let max_cycle = *self.node_table[node_id].keys().max().unwrap();
                let starting_cycles = sys_spec
                    .get_node(*node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .starting_cycles();
                max_cycle - starting_cycles
            })
            .max();
        let max_link_busy = common_links
            .iter()
            .map(|link_id| {
                let max_link_cycle = self.link_table[link_id].keys().max().unwrap();
                let (src, dst) = sys_spec.get_link_endpoints(*link_id);
                let link_action = &self.link_table[link_id][max_link_cycle];
                let mut common_duration = 0;
                if link_action.gather.is_some() {
                    common_duration = max_link_cycle
                        - sys_spec
                            .get_node(src)
                            .borrow()
                            .into_provisioned_node()
                            .unwrap()
                            .starting_cycles();
                }
                if link_action.scatter.is_some() {
                    common_duration = usize::max(
                        common_duration,
                        max_link_cycle
                            - sys_spec
                                .get_node(dst)
                                .borrow()
                                .into_provisioned_node()
                                .unwrap()
                                .starting_cycles(),
                    );
                }
                common_duration
            })
            .max();
        // The infimum offset guarantees an upper bound for which the placement
        // of `other` into `self` must succeed.
        let infimum_offset = 1 + max_node_busy.max(max_link_busy).unwrap();
        for offset in 0..=infimum_offset {
            let result = self.merge(&other, offset);
            match result {
                Result::Err(Error::InvalidMergeOffset) => continue,
                _ => return Ok(self),
            }
        }
        Err(Error::InvalidSchedule)
    }

    pub fn link_calendar(
        &self,
        link_id: &EdgeIndex,
        sys_spec: &HardwareSpec,
    ) -> Result<(Calendar, Calendar), Error> {
        if !self.link_table.contains_key(&link_id) {
            return Ok((vec![], vec![]));
        }
        let link_cycles = &self.link_table[&link_id];
        let link_src_sparse = link_cycles
            .iter()
            .filter_map(|(cycle, action)| {
                action.gather.as_ref().map(|comms_attrs| {
                    (
                        *cycle,
                        CalendarEntry::new(Some(comms_attrs.address as u32), 1),
                    )
                })
            })
            .collect::<HashMap<_, _>>();

        let link_dst_sparse = link_cycles
            .iter()
            .filter_map(|(cycle, action)| {
                action.scatter.as_ref().map(|comms_attrs| {
                    (
                        *cycle,
                        CalendarEntry::new(Some(comms_attrs.address as u32), 1),
                    )
                })
            })
            .collect::<HashMap<_, _>>();
        let (src_node_id, dst_node_id) = sys_spec.get_link_endpoints(*link_id);
        Ok((
            Calendar::compact(
                &link_src_sparse,
                sys_spec
                    .get_node(src_node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .starting_cycles(),
            ),
            Calendar::compact(
                &link_dst_sparse,
                sys_spec
                    .get_node(dst_node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .starting_cycles(),
            ),
        ))
    }

    pub fn switch_calendar(
        &self,
        switch_node_id: &NodeIndex,
        sys_spec: &HardwareSpec,
    ) -> Result<CrossbarCalendar, Error> {
        if !self.node_table.contains_key(switch_node_id) {
            return Ok(vec![]);
        }
        let node_cycles = &self.node_table[switch_node_id];
        if sys_spec
            .get_node(*switch_node_id)
            .borrow()
            .into_provisioned_switch_node()
            .is_none()
        {
            return Err(Error::InvalidNode);
        }
        let sparse_calendar = node_cycles
            .iter()
            .map(|(cycle, action)| {
                if let NodeAction::Switch(rsv) = action {
                    (*cycle, rsv.calendar_entry(sys_spec))
                } else {
                    panic!("Unexpected action associated with a switch.");
                }
            })
            .collect::<HashMap<_, _>>();
        Ok(CrossbarCalendar::compact(
            &sparse_calendar,
            sys_spec
                .get_node(*switch_node_id)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .starting_cycles(),
        ))
    }

    pub fn node_calendar(
        &self,
        node_id: &NodeIndex,
        sys_spec: &HardwareSpec,
    ) -> Result<NodeCalendar, Error> {
        if !self.node_table.contains_key(node_id) {
            return Ok(vec![]);
        }
        let node_cycles = &self.node_table[&node_id];
        if sys_spec
            .get_node(*node_id)
            .borrow()
            .into_provisioned_switch_node()
            .is_some()
        {
            return Err(Error::InvalidNode);
        }
        let sparse_calendar = node_cycles
            .iter()
            .filter_map(|(cycle, action)| {
                if let NodeAction::Compute(run_attrs) = action {
                    return Some((
                        *cycle,
                        NodeCalendarEntry::new(
                            Some(ServiceHandle::new(
                                run_attrs.service_handle.app_id.clone(),
                                run_attrs.service_handle.service_id,
                            )),
                            1,
                        ),
                    ));
                }
                None
            })
            .collect::<HashMap<_, _>>();
        Ok(NodeCalendar::compact(
            &sparse_calendar,
            sys_spec
                .get_node(*node_id)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .starting_cycles(),
        ))
    }
}

pub fn concat_scheduler<const BUFFERING: Buffering>(
    app_specs: &[&Application],
    sys_spec: &HardwareSpec,
    allocation: &SystemAllocation,
) -> Result<[ReservationTable; BUFFERING], Error> {
    match BUFFERING {
        BUFFERING_DOUBLE => {
            // This is a simple (unoptimizing) scheduler, and we don't make an effort to
            // balance the applications in the double-buffering scenario.
            if app_specs.is_empty() {
                log::error!("No applications to schedule!");
                return Err(Error::InvalidSchedule);
            }
            let mut reservations = [(); BUFFERING].map(|_| vec![]);
            for (i, (mut compute_reservations, mut comms_reservations)) in app_specs
                .iter()
                .map(|app_spec| ReservationTable::new_reservations(app_spec, sys_spec, allocation))
                .enumerate()
            {
                let buffer = i % BUFFERING_DOUBLE;
                if buffer == 0 {
                    reservations[0].append(&mut compute_reservations);
                    reservations[1].append(&mut comms_reservations);
                }
                if buffer == 1 {
                    reservations[0].append(&mut comms_reservations);
                    reservations[1].append(&mut compute_reservations);
                }
            }
            let mut result = [(); BUFFERING].map(|_| ReservationTable::new());
            for i in 0..BUFFERING {
                for rsv in &reservations[i] {
                    result[i].concat(&rsv, sys_spec)?;
                }
            }
            Ok(result)
        }
        BUFFERING_SINGLE => {
            unimplemented!("Single buffered concat scheduling not yet implemented.")
        }
        _ => {
            panic!("Unsupported buffering configuration!");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::app::CommsHandle;
    use crate::mailbox::MailBox;
    use crate::ports::PortLabel;
    use crate::ports::PortProperties;
    use crate::scheduler::generate_physical_system_1x1_network;
    use crate::specs::ApplicationNode;
    use crate::specs::SystemContext;
    use crate::Connection;
    use crate::DataWithValidity;
    use crate::FramingLead;
    use crate::Frequency;
    use crate::FrequencyFactor;
    use crate::InputFrameRef;
    use crate::Latency;
    use crate::LoopbackRef;
    use crate::OutputFrameRef;
    use crate::Service;
    use bits::Bits;

    const MSG_SIZE: usize = std::mem::size_of::<u8>() * 8;
    const FRAME_SIZE: usize = 1;

    const DEFAULT_LATENCY: Latency = Latency(1);
    const SVC0_COMPUTE_CYCLES: usize = 1;
    const SVC1_COMPUTE_CYCLES: usize = 2;
    const SVC2_COMPUTE_CYCLES: usize = 3;

    fn simple_service_action(
        state: LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        let next = inputs[0].map(|b| u8::unpack(b)).unwrap_or(0) + 1;
        state
            .unwrap()
            .copy_from_bitslice(u8::pack(&next).as_bitslice());
        *outputs[0] = DataWithValidity {
            data: u8::pack(&next).into_boxed_bitslice(),
            valid: true,
        };
    }

    fn build_simple_app() -> Application {
        // +------+
        // | svc0 | -+
        // +------+  |
        //   |       |
        //   |       |
        //   v       |
        // +------+  |
        // | svc1 |  |
        // +------+  |
        //   |       |
        //   |       |
        //   v       |
        // +------+  |
        // | svc2 | <+
        // +------+

        let svc0 = Service::new(
            "svc0",
            simple_service_action,
            Some(u8::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        );
        let svc1 = Service::new(
            "svc1",
            simple_service_action,
            Some(u8::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        );
        let svc2 = Service::new(
            "svc2",
            simple_service_action,
            Some(u8::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        );
        let conn = Connection::new_for_testing(0, 0, MSG_SIZE);
        let mut app = Application::new();
        let svc0_id = app.add_node(svc0);
        let svc1_id = app.add_node(svc1);
        let svc2_id = app.add_node(svc2);
        app.link_simplex_framing(svc0_id, svc1_id, conn.clone(), FramingLead::Src);
        app.link_simplex_framing(svc1_id, svc2_id, conn.clone(), FramingLead::Src);
        app.link_simplex_framing(
            svc0_id,
            svc2_id,
            Connection::new_for_testing(1, 1, MSG_SIZE),
            FramingLead::Src,
        );
        // app.link_simplex_framing(svc0_id, svc1_id, link, framing_lead)
        app.get_node(svc0_id)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[
                (
                    PortLabel::Number(0),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(MSG_SIZE),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(1),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(MSG_SIZE),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                ),
            ]);
        app.get_node(svc1_id)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[
                (
                    PortLabel::Number(0),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(MSG_SIZE),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(1),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(MSG_SIZE),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                ),
            ]);
        app.get_node(svc2_id)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[
                (
                    PortLabel::Number(0),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(MSG_SIZE),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(1),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(MSG_SIZE),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
            ]);
        app
    }

    #[derive(Debug)]
    struct TestFixture {
        app_spec: Application,
        sys_spec: HardwareSpec,
        alloc: SystemAllocation,
        switch_nodes: HashMap<NodeIndex, NodeIndex>,
    }

    enum Fixture {
        UniFreqNoConflict,
        UniFreqConflict,
        UniFreqSwitchConflict,
    }

    enum StartingCycles {
        Uniform(Cycle),
        NonUniform(HashMap<NodeIndex, Cycle>),
    }

    fn test_fixture(variant: Fixture, starting_cycles: Option<StartingCycles>) -> TestFixture {
        let app_spec = build_simple_app();
        let mapping_cfg = &crate::MappingConfiguration1x1Network {
            node_frequency: Frequency::new(1),
            link_frequency: Frequency::new(1),
            link_latency: DEFAULT_LATENCY,
            frame_size: FRAME_SIZE,
            crossbar_latency: DEFAULT_LATENCY,
            compute_cycles_per_service_node: 1,
            ..Default::default()
        };
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            |         |
        //            |         |
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            |
        //    |            |
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | --> | svc1 |
        //    |     |             | <-- |      |
        //    |     +-------------+     +------+
        //    |            |
        //    |            |
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            |         |
        //            |         |
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+

        let mut sys_spec = generate_physical_system_1x1_network(&app_spec, mapping_cfg);

        // We allocate explicitly for predictable testing.
        let svc0_id = app_spec.get_node_index_by_name("svc0").unwrap();
        let svc1_id = app_spec.get_node_index_by_name("svc1").unwrap();
        let svc2_id = app_spec.get_node_index_by_name("svc2").unwrap();
        let svc0_sys_id = sys_spec
            .iter_nodes()
            .find(|node_id| sys_spec.get_output_links(*node_id).count() == 2)
            .unwrap();
        let svc1_sys_id = sys_spec
            .iter_nodes()
            .find(|node_id| sys_spec.get_input_links(*node_id).count() == 1)
            .unwrap();
        let svc2_sys_id = sys_spec
            .iter_nodes()
            .find(|node_id| sys_spec.get_input_links(*node_id).count() == 2)
            .unwrap();
        let node_mapping = HashMap::from([
            (svc0_id, svc0_sys_id),
            (svc1_id, svc1_sys_id),
            (svc2_id, svc2_sys_id),
        ]);
        let switch_nodes = sys_spec
            .compute_nodes()
            .iter()
            .map(|sys_node_id| {
                if sys_spec.get_output_links(*sys_node_id).count() == 0 {
                    // svc2 has no outputs
                    let edge_ref = sys_spec.get_input_links(*sys_node_id).next().unwrap();
                    let (switch_node_id, _) = sys_spec.get_link_endpoints(edge_ref.id());
                    (*sys_node_id, switch_node_id)
                } else {
                    let edge_ref = sys_spec.get_output_links(*sys_node_id).next().unwrap();
                    let (_, switch_node_id) = sys_spec.get_link_endpoints(edge_ref.id());
                    (*sys_node_id, switch_node_id)
                }
            })
            .collect::<HashMap<_, _>>();

        // Notation -(i)-> : the ith edge, when multiple are present
        //
        // app path: svc0 -> svc1, sys path: svc0 -(0)-> switch0 -> switch1 -> svc1
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            #         |
        //            #         |
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | ##> | svc1 |
        //    |     |             | <-- |      |
        //    |     +-------------+     +------+
        //    |            |
        //    |            |
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            |         |
        //            |         |
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let path_components_svc0_svc1 = vec![
            // svc0 -> switch0
            sys_spec
                .get_output_links(svc0_sys_id)
                .filter(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc0_sys_id]
                })
                .map(|e| e.id())
                .next()
                .unwrap(),
            // switch0 -> switch1
            sys_spec
                .get_output_links(switch_nodes[&svc0_sys_id])
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc1_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch1 -> svc1
            sys_spec
                .get_output_links(switch_nodes[&svc1_sys_id])
                .find(|edge_ref| sys_spec.get_link_endpoints(edge_ref.id()).1 == svc1_sys_id)
                .map(|e| e.id())
                .unwrap(),
        ];
        let path_svc0_svc1 = Path::new(path_components_svc0_svc1.as_slice()).unwrap();

        // app path svc1 -> svc2, sys path: svc1 -> switch1 -> switch2 -(0)-> svc2
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            |         |
        //            |         |
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            |
        //    |            |
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | --> | svc1 |
        //    |     |             | <## |      |
        //    |     +-------------+     +------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            #         |
        //            #         |
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let path_components_svc1_svc2 = vec![
            // svc1 -> switch1
            sys_spec
                .get_output_links(svc1_sys_id)
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc1_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch1 -> switch2
            sys_spec
                .get_output_links(switch_nodes[&svc1_sys_id])
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc2_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch2 -> svc2
            sys_spec
                .get_output_links(switch_nodes[&svc2_sys_id])
                .filter(|edge_ref| sys_spec.get_link_endpoints(edge_ref.id()).1 == svc2_sys_id)
                .map(|e| e.id())
                .next()
                .unwrap(),
        ];
        let path_svc1_svc2 = Path::new(path_components_svc1_svc2.as_slice()).unwrap();

        // app path svc0 -> svc2, sys path: svc0 -(1)-> switch0 -> switch2 -(1)-> svc2
        //
        // non-conflicting path
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //    ##### | svc0_switch |
        //    #     +-------------+
        //    #            |
        //    #            |
        //    #            v
        //    #     +-------------+     +------+
        //    #     | svc1_switch | --> | svc1 |
        //    #     |             | <-- |      |
        //    #     +-------------+     +------+
        //    #            |
        //    #            |
        //    #            v
        //    #     +-------------+
        //    ####> | svc2_switch |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let path_components_svc0_svc2 = vec![
            // svc0 -> switch0
            sys_spec
                .get_output_links(svc0_sys_id)
                .filter(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc0_sys_id]
                })
                .map(|e| e.id())
                .last()
                .unwrap(),
            // switch0 -> switch2
            sys_spec
                .get_output_links(switch_nodes[&svc0_sys_id])
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc2_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch2 -> svc2
            sys_spec
                .get_output_links(switch_nodes[&svc2_sys_id])
                .filter(|edge_ref| sys_spec.get_link_endpoints(edge_ref.id()).1 == svc2_sys_id)
                .map(|e| e.id())
                .last()
                .unwrap(),
        ];

        let path_svc0_svc2 = Path::new(path_components_svc0_svc2.as_slice()).unwrap();

        // app path svc0 -> svc2, sys path: svc0 -(0)-> switch0 -> switch1 -> switch2 -(0)-> svc2
        //
        // This path {conflicts} with both:
        //   1. svc0 -> svc1: {svc0 -(0)-> switch0} -> switch1 -> svc1                   source conflict
        //   2. svc1 -> svc2: 1st conflict svc1 -> {switch1 -> switch2} -(0)-> svc2      switch conflict
        //                    2nd conflict svc1 ->  switch1 -> {switch2 -(0)-> svc2}     dest. conflict
        //
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            #         |
        //            #         |
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | --> | svc1 |
        //    |     |             | <-- |      |
        //    |     +-------------+     +------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            #         |
        //            #         |
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let path_components_svc0_svc2_conflict = vec![
            // svc0 -> switch0
            sys_spec
                .get_output_links(svc0_sys_id)
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc0_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch0 -> switch1
            sys_spec
                .get_output_links(switch_nodes[&svc0_sys_id])
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc1_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch1 -> switch2
            sys_spec
                .get_output_links(switch_nodes[&svc1_sys_id])
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc2_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch2 -> svc2
            sys_spec
                .get_output_links(switch_nodes[&svc2_sys_id])
                .filter(|edge_ref| sys_spec.get_link_endpoints(edge_ref.id()).1 == svc2_sys_id)
                .map(|e| e.id())
                .next()
                .unwrap(),
        ];
        let path_svc0_svc2_conflict =
            Path::new(path_components_svc0_svc2_conflict.as_slice()).unwrap();

        // app path svc0 -> svc2, sys path: svc0 -(1)-> switch0 -> switch1 -> switch2 -(1)-> svc2
        //
        // A different {conflicting} path, conflicting on switch1's ingress & egress
        //   svc0 -> svc1: conflict svc0 -(0)-> {switch0 -> switch1} -> svc1
        //   svc1 -> svc2: conflict svc1 -> {switch1 -> switch2} -(0)-> svc2
        //
        //
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | --> | svc1 |
        //    |     |             | <-- |      |
        //    |     +-------------+     +------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let path_components_svc0_svc2_switch_conflict = vec![
            // svc0 -> switch0
            sys_spec
                .get_output_links(svc0_sys_id)
                .filter(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc0_sys_id]
                })
                .map(|e| e.id())
                .last()
                .unwrap(),
            // switch0 -> switch1
            sys_spec
                .get_output_links(switch_nodes[&svc0_sys_id])
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc1_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch1 -> switch2
            sys_spec
                .get_output_links(switch_nodes[&svc1_sys_id])
                .find(|edge_ref| {
                    sys_spec.get_link_endpoints(edge_ref.id()).1 == switch_nodes[&svc2_sys_id]
                })
                .map(|e| e.id())
                .unwrap(),
            // switch2 -> svc2
            sys_spec
                .get_output_links(switch_nodes[&svc2_sys_id])
                .filter(|edge_ref| sys_spec.get_link_endpoints(edge_ref.id()).1 == svc2_sys_id)
                .map(|e| e.id())
                .last()
                .unwrap(),
        ];
        let path_svc0_svc2_switch_conflict =
            Path::new(path_components_svc0_svc2_switch_conflict.as_slice()).unwrap();

        let svc0_svc1_conn_id = app_spec
            .get_output_links(svc0_id)
            .find(|e| app_spec.get_link_endpoints(e.id()).1 == svc1_id)
            .unwrap()
            .id();
        let svc1_svc2_conn_id = app_spec.get_output_links(svc1_id).next().unwrap().id();
        let svc0_svc2_conn_id = app_spec
            .get_output_links(svc0_id)
            .find(|e| app_spec.get_link_endpoints(e.id()).1 == svc2_id)
            .unwrap()
            .id();

        let link_mapping = HashMap::from([
            (
                CommsHandle::new(app_spec.id(), svc0_svc1_conn_id),
                Some(path_svc0_svc1.clone()),
            ),
            (
                CommsHandle::new(app_spec.id(), svc1_svc2_conn_id),
                Some(path_svc1_svc2.clone()),
            ),
            (
                CommsHandle::new(app_spec.id(), svc0_svc2_conn_id),
                Some(path_svc0_svc2),
            ),
        ]);

        let link_mapping_conflict = HashMap::from([
            (
                CommsHandle::new(app_spec.id(), svc0_svc1_conn_id),
                Some(path_svc0_svc1.clone()),
            ),
            (
                CommsHandle::new(app_spec.id(), svc1_svc2_conn_id),
                Some(path_svc1_svc2.clone()),
            ),
            (
                CommsHandle::new(app_spec.id(), svc0_svc2_conn_id),
                Some(path_svc0_svc2_conflict),
            ),
        ]);

        let link_mapping_switch_conflict = HashMap::from([
            (
                CommsHandle::new(app_spec.id(), svc0_svc1_conn_id),
                Some(path_svc0_svc1),
            ),
            (
                CommsHandle::new(app_spec.id(), svc1_svc2_conn_id),
                Some(path_svc1_svc2),
            ),
            (
                CommsHandle::new(app_spec.id(), svc0_svc2_conn_id),
                Some(path_svc0_svc2_switch_conflict),
            ),
        ]);

        let nodes = node_mapping
            .iter()
            .map(|(app_node_id, sys_node_id)| {
                (
                    ServiceHandle::new(app_spec.id(), *app_node_id),
                    *sys_node_id,
                )
            })
            .collect::<HashMap<_, _>>();
        let compute_cycles = HashMap::from([
            (
                ServiceHandle::new(app_spec.id(), svc0_id),
                SVC0_COMPUTE_CYCLES,
            ),
            (
                ServiceHandle::new(app_spec.id(), svc1_id),
                SVC1_COMPUTE_CYCLES,
            ),
            (
                ServiceHandle::new(app_spec.id(), svc2_id),
                SVC2_COMPUTE_CYCLES,
            ),
        ]);

        fn associate_mailboxes(
            app_spec: &Application,
            sys_spec: &mut HardwareSpec,
            alloc: &SystemAllocation,
        ) {
            let mut knapsack: HashMap<NodeIndex, Vec<NodeIndex>> = HashMap::new();
            for (app_node_id, node_id) in &alloc.nodes {
                if !knapsack.contains_key(&node_id) {
                    knapsack.insert(*node_id, vec![app_node_id.service_id]);
                } else {
                    knapsack
                        .get_mut(&node_id)
                        .unwrap()
                        .push(app_node_id.service_id);
                }
            }
            assert!(knapsack
                .values()
                .all(|service_assignments| service_assignments.len() == 1));
            assert!(alloc
                .links
                .values()
                .filter(|path| path.is_some())
                .all(|path| path.as_ref().unwrap().destinations().len() == 1));
            let mut mailboxes = app_spec
                .iter_nodes()
                .map(|app_node_id| (app_node_id, MailBox::new(app_spec, &[app_node_id])))
                .collect::<HashMap<_, _>>();
            for app_node_id in app_spec.iter_nodes() {
                for edge_ref in app_spec.get_output_links(app_node_id) {
                    let app_edge = CommsHandle::new(app_spec.id(), edge_ref.id());
                    mailboxes
                        .get_mut(&app_node_id)
                        .unwrap()
                        .map_connection_src_to_gather(
                            app_edge.clone(),
                            sys_spec,
                            alloc.links[&app_edge.clone()].as_ref().unwrap().source(),
                        )
                        .unwrap();
                }
                for edge_ref in app_spec.get_input_links(app_node_id) {
                    let app_edge = CommsHandle::new(app_spec.id(), edge_ref.id());
                    mailboxes
                        .get_mut(&app_node_id)
                        .unwrap()
                        .map_connection_dst_to_scatter(
                            app_edge.clone(),
                            sys_spec,
                            alloc.links[&app_edge.clone()]
                                .as_ref()
                                .unwrap()
                                .destinations()[0],
                        )
                        .unwrap();
                }
            }
            for (app_node_id, mut mailbox) in mailboxes.drain() {
                let app_node = ServiceHandle::new(app_spec.id(), app_node_id);
                let sys_node_id = alloc.nodes[&app_node];
                mailbox.materialize_addresses(&sys_spec).unwrap();
                sys_spec
                    .get_node(sys_node_id)
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_mailbox(mailbox);
            }
        }

        let result = match variant {
            Fixture::UniFreqNoConflict => {
                let alloc = SystemAllocation {
                    nodes: nodes,
                    links: link_mapping,
                    compute_cycles: compute_cycles,
                };
                associate_mailboxes(&app_spec, &mut sys_spec, &alloc);
                TestFixture {
                    app_spec,
                    sys_spec,
                    alloc,
                    switch_nodes,
                }
            }
            Fixture::UniFreqConflict => {
                let alloc = SystemAllocation {
                    nodes: nodes,
                    links: link_mapping_conflict,
                    compute_cycles: compute_cycles,
                };
                associate_mailboxes(&app_spec, &mut sys_spec, &alloc);
                TestFixture {
                    app_spec,
                    sys_spec,
                    alloc: alloc,
                    switch_nodes,
                }
            }
            Fixture::UniFreqSwitchConflict => {
                let alloc = SystemAllocation {
                    nodes: nodes,
                    links: link_mapping_switch_conflict,
                    compute_cycles: compute_cycles,
                };
                associate_mailboxes(&app_spec, &mut sys_spec, &alloc);
                TestFixture {
                    app_spec,
                    sys_spec,
                    alloc: alloc,
                    switch_nodes,
                }
            }
        };
        if let Some(starting_cycles) = starting_cycles {
            for node_id in result.sys_spec.iter_nodes() {
                result
                    .sys_spec
                    .get_node(node_id)
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_starting_cycles(match &starting_cycles {
                        StartingCycles::Uniform(value) => *value,
                        StartingCycles::NonUniform(starting_cycles) => starting_cycles[&node_id],
                    });
            }
        }
        result
    }

    impl TestFixture {
        fn get_app_link(&self, src_node: &NodeIndex, dst_node: &NodeIndex) -> EdgeIndex {
            self.app_spec
                .get_output_links(*src_node)
                .find(|edge_ref| self.app_spec.get_link_endpoints(edge_ref.id()).1 == *dst_node)
                .map(|e| e.id())
                .unwrap()
        }

        fn get_outbox(&self, app_link: &EdgeIndex) -> mailbox::ConnectionAttrs {
            let (src, _) = self.app_spec.get_link_endpoints(*app_link);
            let sys_node = self.alloc.nodes[&ServiceHandle::new(self.app_spec.id(), src)];
            self.sys_spec
                .get_node(sys_node)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .get_mailbox()
                .unwrap()
                .outboxes
                .iter()
                .find(|comms_attrs| {
                    comms_attrs.connection_id == CommsHandle::new(self.app_spec.id(), *app_link)
                })
                .unwrap()
                .clone()
        }

        fn link_endpoint_start_times(&self, sys_link_id: &EdgeIndex) -> (Cycle, Cycle) {
            let (src_sys_id, dst_sys_id) = self.sys_spec.get_link_endpoints(*sys_link_id);
            (
                self.sys_spec
                    .get_node(src_sys_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .starting_cycles(),
                self.sys_spec
                    .get_node(dst_sys_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .starting_cycles(),
            )
        }
    }

    #[test]
    fn test_new_compute_reservation() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let rsv = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc0_id),
        );
        let svc0_sys_id = fixture.alloc.nodes[&ServiceHandle::new(fixture.app_spec.id(), svc0_id)];
        assert!(rsv.node_table.contains_key(&svc0_sys_id));
        let svc0_start_cycles = fixture
            .sys_spec
            .get_node(svc0_sys_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        for k in 0..SVC0_COMPUTE_CYCLES {
            let cycle = svc0_start_cycles + k;
            assert!(rsv.node_table[&svc0_sys_id].contains_key(&cycle));
            match &rsv.node_table[&svc0_sys_id][&cycle] {
                NodeAction::Compute(run_attrs) => {
                    assert_eq!(
                        run_attrs.service_handle,
                        ServiceHandle::new(fixture.app_spec.id(), svc0_id)
                    );
                }
                _ => assert!(false),
            }
        }
    }

    #[test]
    fn test_new_comms_reservation() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();
        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);
        let path = &fixture.alloc.links
            [&CommsHandle::new(fixture.app_spec.id(), svc0_svc2_conn_id)]
            .as_ref()
            .unwrap();
        let (svc0_sys_id, _) = fixture.sys_spec.get_link_endpoints(path.source());
        let outbox = fixture.get_outbox(&svc0_svc2_conn_id);
        let rsv =
            ReservationTable::new_comms_reservation(&fixture.sys_spec, &fixture.alloc, &[&outbox]);
        // transfer 8 Frames, 1-bit wide
        // path: svc0 -> svc0_switch -> svc2_switch -> svc2
        //
        // For each resource, list the cycles in which they are busy and
        // the operation they will be performing {op}
        //
        // resource{op}: x, y, z, ...
        //
        // k0 = start_time(svc0)
        // (svc0 -> svc0_switch){gather}: k0 + 0, 1, 2, 3, 4, 5, 6, 7
        //
        // k1 = k0 + ugn(svc0, svc0_switch)
        // (svc0 -> svc0_switch){scatter}: k1 + (0, 1, ..., 7)
        //
        // k2 = k1 + crossbar_latency(svc0_switch)
        // svc0_switch{crossbar} = k2 + (0, 1, ..., 7)
        //
        // k3 = k2 + 1
        // (svc0_switch -> svc2_switch){gather}: k3 + (0, 1, ..., 7)
        //
        // k4 = k3 + logical_latency(svc0_switch + svc2_switch)
        // (svc0_switch -> svc2_switch){scatter} = k4 + (0, 1, ..., 7)
        //
        // k5 = k4 + crossbar_latency(svc2_switch)
        // svc2_switch{crossbar} = k5 + (0, 1, ..., 7)
        //
        // k6 = k5 + 1
        // (svc2_switch -> svc2){gather}: k6 + (0, 1, ..., 7)
        //
        // k7 = k6 + logical_latency(svc2_switch, svc2)
        // (svc2_switch -> svc2){scatter} = k7 + (0, 1, ..., 7)
        let path_hops: HashMap<EdgeIndex, Vec<EdgeIndex>> =
            HashMap::from_iter(path.switch_hops().drain(..));
        let svc0_switch_id = fixture.switch_nodes[&svc0_sys_id];
        let svc0_svc0_switch_link_id = path.source();
        let svc0_starting_cycles = fixture
            .sys_spec
            .get_node(svc0_sys_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        // k0 = start_time(svc0)
        // (svc0 -> svc0_switch){gather}: k0 + 0, 1, 2, 3, 4, 5, 6, 7
        let k0 = svc0_starting_cycles;
        for frame_idx in 0..MSG_SIZE {
            let cycle = k0 + frame_idx;
            assert!(rsv.link_table[&svc0_svc0_switch_link_id].contains_key(&cycle));
            let link_action = &rsv.link_table[&svc0_svc0_switch_link_id][&cycle];
            assert!(link_action.gather.is_some());
            assert_eq!(
                link_action.gather.as_ref().unwrap().address - frame_idx,
                outbox
                    .mapped_endpoint
                    .as_ref()
                    .unwrap()
                    .base_address
                    .unwrap()
            );
            assert_eq!(link_action.gather.as_ref().unwrap().path_idx.0, 0);
        }
        // k1 = k0 + ugn(svc0, svc0_switch)
        // (svc0 -> svc0_switch){scatter}: k1 + (0, 1, ..., 7)
        let svc0_switch_starting_cycles = fixture
            .sys_spec
            .get_node(svc0_switch_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        assert!(
            k0 as i64 + fixture.sys_spec.ugn(svc0_svc0_switch_link_id)
                > svc0_switch_starting_cycles as i64
        );
        let k1 = (k0 as i64 + fixture.sys_spec.ugn(svc0_svc0_switch_link_id)) as usize;
        for frame_idx in 0..MSG_SIZE {
            let cycle = k1 + frame_idx;
            assert!(rsv.link_table[&svc0_svc0_switch_link_id].contains_key(&cycle));
            let link_action = &rsv.link_table[&svc0_svc0_switch_link_id][&cycle];
            assert!(link_action.scatter.is_some());
            assert_eq!(link_action.scatter.as_ref().unwrap().address, 0)
        }
        let svc0_switch_crossbar_latency = fixture
            .sys_spec
            .get_node(svc0_switch_id)
            .borrow()
            .into_provisioned_switch_node()
            .unwrap()
            .crossbar_latency()
            .0;
        assert_eq!(path_hops[&svc0_svc0_switch_link_id].len(), 1);
        let svc0_switch_svc2_switch_link_id = path_hops[&svc0_svc0_switch_link_id][0];
        let k2 = k1 + svc0_switch_crossbar_latency;
        // k2 = k1 + crossbar_latency(svc0_switch)
        // svc0_switch{crossbar} = k2 + (0, 1, ..., 7)
        for frame_idx in 0..MSG_SIZE {
            let cycle = k2 + frame_idx;
            assert!(rsv.node_table[&svc0_switch_id].contains_key(&cycle));
            let node_action = &rsv.node_table[&svc0_switch_id][&cycle];
            match node_action {
                NodeAction::Switch(switch_rsv) => {
                    assert_eq!(
                        switch_rsv.muxes,
                        HashMap::from_iter([(
                            svc0_svc0_switch_link_id,
                            vec![svc0_switch_svc2_switch_link_id]
                        )])
                    );
                    assert_eq!(switch_rsv.path_idx.0, 0);
                }
                _ => assert!(false),
            };
        }
        // k3 = k2 + 1
        // (svc0_switch -> svc2_switch){gather}: k3 + (0, 1, ..., 7)
        let k3 = k2 + 1;
        for frame_idx in 0..MSG_SIZE {
            let cycle = k3 + frame_idx;
            assert!(rsv.link_table[&svc0_switch_svc2_switch_link_id].contains_key(&cycle));
            let link_action = &rsv.link_table[&svc0_switch_svc2_switch_link_id][&cycle];
            assert!(link_action.gather.is_some());
            assert_eq!(link_action.gather.as_ref().unwrap().address, 0);
            assert_eq!(link_action.gather.as_ref().unwrap().path_idx.0, 0);
        }
        // k4 = k3 + logical_latency(svc0_switch + svc2_switch)
        // (svc0_switch -> svc2_switch){scatter} = k4 + (0, 1, ..., 7)
        assert_eq!(path_hops[&svc0_switch_svc2_switch_link_id].len(), 1);
        let svc2_switch_svc2_link_id = path_hops[&svc0_switch_svc2_switch_link_id][0];
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();
        let svc2_sys_id = fixture.alloc.nodes[&ServiceHandle::new(fixture.app_spec.id(), svc2_id)];
        let svc2_switch_id = fixture.switch_nodes[&svc2_sys_id];
        let svc2_switch_starting_cycles = fixture
            .sys_spec
            .get_node(svc2_switch_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        assert!(
            k3 as i64 + fixture.sys_spec.ugn(svc0_switch_svc2_switch_link_id)
                > svc2_switch_starting_cycles as i64
        );
        let k4 = (k3 as i64 + fixture.sys_spec.ugn(svc0_switch_svc2_switch_link_id)) as usize;
        for frame_idx in 0..MSG_SIZE {
            let cycle = k4 + frame_idx;
            assert!(rsv.link_table[&svc0_switch_svc2_switch_link_id].contains_key(&cycle));
            let link_action = &rsv.link_table[&svc0_switch_svc2_switch_link_id][&cycle];
            assert!(link_action.scatter.is_some());
            assert_eq!(link_action.scatter.as_ref().unwrap().address, 0);
            assert_eq!(link_action.scatter.as_ref().unwrap().path_idx.0, 0);
        }
        // k5 = k4 + crossbar_latency(svc2_switch)
        // svc2_switch{crossbar} = k5 + (0, 1, ..., 7)
        let svc2_switch_crossbar_latency = fixture
            .sys_spec
            .get_node(svc2_switch_id)
            .borrow()
            .into_provisioned_switch_node()
            .unwrap()
            .crossbar_latency()
            .0;
        let k5 = k4 + svc2_switch_crossbar_latency;
        for frame_idx in 0..MSG_SIZE {
            let cycle = k5 + frame_idx;
            assert!(rsv.node_table[&svc2_switch_id].contains_key(&cycle));
            let node_action = &rsv.node_table[&svc2_switch_id][&cycle];
            match node_action {
                NodeAction::Switch(switch_rsv) => {
                    assert_eq!(
                        switch_rsv.muxes,
                        HashMap::from([(
                            svc0_switch_svc2_switch_link_id,
                            vec![svc2_switch_svc2_link_id]
                        )])
                    );
                    assert_eq!(switch_rsv.path_idx.0, 0);
                }
                _ => assert!(false),
            };
        }
        // k6 = k5 + 1
        // (svc2_switch -> svc2){gather}: k6 + (0, 1, ..., 7)
        let k6 = k5 + 1;
        for frame_idx in 0..MSG_SIZE {
            let cycle = k6 + frame_idx;
            assert!(rsv.link_table[&svc2_switch_svc2_link_id].contains_key(&cycle));
            let link_action = &rsv.link_table[&svc2_switch_svc2_link_id][&cycle];
            assert!(link_action.gather.is_some());
            assert_eq!(link_action.gather.as_ref().unwrap().address, 0);
            assert_eq!(link_action.gather.as_ref().unwrap().path_idx.0, 0);
        }
        // k7 = k6 + logical_latency(svc2_switch, svc2)
        // (svc2_switch -> svc2){scatter} = k7 + (0, 1, ..., 7)
        let svc2_start_time = fixture
            .sys_spec
            .get_node(svc2_sys_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        assert!(
            k6 as i64 + fixture.sys_spec.ugn(svc2_switch_svc2_link_id) > svc2_start_time as i64,
        );
        let k7 = (k6 as i64 + fixture.sys_spec.ugn(svc2_switch_svc2_link_id)) as usize;
        let svc2_inbox = fixture
            .sys_spec
            .get_node(svc2_sys_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .get_mailbox()
            .unwrap()
            .inboxes
            .iter()
            .find(|inbox| {
                inbox.connection_id == CommsHandle::new(fixture.app_spec.id(), svc0_svc2_conn_id)
            })
            .unwrap()
            .clone();
        for frame_idx in 0..MSG_SIZE {
            let cycle = k7 + frame_idx;
            assert!(rsv.link_table[&svc2_switch_svc2_link_id].contains_key(&cycle));
            let link_action = &rsv.link_table[&svc2_switch_svc2_link_id][&cycle];
            assert!(link_action.scatter.is_some());
            assert_eq!(
                link_action.scatter.as_ref().unwrap().address - frame_idx,
                svc2_inbox
                    .mapped_endpoint
                    .as_ref()
                    .unwrap()
                    .base_address
                    .unwrap()
            );
            assert_eq!(link_action.scatter.as_ref().unwrap().path_idx.0, 0)
        }
    }

    #[test]
    fn test_conflicting_paths_fuzzed_ugns() {
        // This test is different than other conflicting paths tests because the
        // path visits the same set of nodes en route (via different links), and
        // can test with "fuzzed UGNs" (since starting cycles are randomly
        // generated).

        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            #         |
        //            #         |
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | --> | svc1 |
        //    |     |             | <-- |      |
        //    |     +-------------+     +------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            #         |
        //            #         |
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let fixture_conflict = test_fixture(Fixture::UniFreqConflict, None);
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | --> | svc1 |
        //    |     |             | <-- |      |
        //    |     +-------------+     +------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        //
        //
        // Note: because all link latencies are configured to be the same,
        // setting the same starting times ensures equal UGNs. (Equivalent UGNs
        // are critical for this test since we want to manually trace the
        // conflicts.)
        let fixture_switch_conflict = test_fixture(
            Fixture::UniFreqSwitchConflict,
            Some(StartingCycles::NonUniform(
                fixture_conflict
                    .sys_spec
                    .iter_nodes()
                    .map(|node_id| {
                        (
                            node_id,
                            fixture_conflict
                                .sys_spec
                                .get_node(node_id)
                                .borrow()
                                .into_provisioned_node()
                                .unwrap()
                                .starting_cycles(),
                        )
                    })
                    .collect::<HashMap<_, _>>(),
            )),
        );

        let svc0_id = fixture_conflict
            .app_spec
            .get_node_index_by_name("svc0")
            .unwrap();
        let svc2_id = fixture_conflict
            .app_spec
            .get_node_index_by_name("svc2")
            .unwrap();
        assert_eq!(
            fixture_switch_conflict
                .app_spec
                .get_node(svc0_id)
                .borrow()
                .name(),
            "svc0"
        );
        assert_eq!(
            fixture_switch_conflict
                .app_spec
                .get_node(svc2_id)
                .borrow()
                .name(),
            "svc2"
        );
        let svc0_svc2_conn_id = fixture_conflict.get_app_link(&svc0_id, &svc2_id);
        let svc0_sys_id = fixture_conflict.alloc.nodes
            [&ServiceHandle::new(fixture_conflict.app_spec.id(), svc0_id)];
        let outbox_conflict = fixture_conflict.get_outbox(&svc0_svc2_conn_id);
        let outbox_switch_conflict = fixture_switch_conflict.get_outbox(&svc0_svc2_conn_id);
        let rsv_conflict = ReservationTable::new_comms_reservation(
            &fixture_conflict.sys_spec,
            &fixture_conflict.alloc,
            &[&outbox_conflict],
        );
        let rsv_switch_conflict = ReservationTable::new_comms_reservation(
            &fixture_switch_conflict.sys_spec,
            &fixture_switch_conflict.alloc,
            &[&outbox_switch_conflict],
        );
        assert_eq!(
            rsv_conflict
                .node_table
                .keys()
                .collect::<HashSet<_>>()
                .intersection(
                    &rsv_switch_conflict
                        .node_table
                        .keys()
                        .collect::<HashSet<_>>()
                )
                .map(|x| **x)
                .collect::<HashSet<_>>(),
            rsv_conflict.common_nodes(&rsv_switch_conflict)
        );
        assert_eq!(
            rsv_conflict
                .link_table
                .keys()
                .collect::<HashSet<_>>()
                .intersection(
                    &rsv_switch_conflict
                        .link_table
                        .keys()
                        .collect::<HashSet<_>>()
                )
                .map(|x| **x)
                .collect::<HashSet<_>>(),
            rsv_conflict.common_links(&rsv_switch_conflict)
        );
        for link_id in fixture_conflict.sys_spec.iter_links() {
            assert_eq!(
                fixture_conflict.sys_spec.ugn(link_id),
                fixture_switch_conflict.sys_spec.ugn(link_id)
            );
        }
        // The two paths will conflict at the switch until the offset exceeds
        // the number of frames being transmitted (MSG_SIZE).
        for offset in 0..=MSG_SIZE {
            if offset < MSG_SIZE {
                assert!(rsv_conflict.conflicts(&rsv_switch_conflict, 0));
            } else {
                assert!(!rsv_conflict.conflicts(&rsv_switch_conflict, MSG_SIZE));
            }
        }
        // Assert they conflict where we expect since
        // ReservationTable::conflicts will simply report if there is a conflict,
        // and not the location (the first it finds)
        //
        // 1. crossbar of svc0_switch
        // 2. egress of svc0_switch (ingress of svc1_switch)
        // 3. crossbar of svc1_switch
        // 4. egress of svc1_switch (ingress of svc2_switch)

        let svc0_tx_cycles = fixture_conflict
            .sys_spec
            .get_node(svc0_sys_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        // 1. crossbar of svc0_switch
        let conflict_path = &fixture_conflict.alloc.links
            [&CommsHandle::new(fixture_conflict.app_spec.id(), svc0_svc2_conn_id)]
            .as_ref()
            .unwrap();
        let switch_conflict_path = &fixture_switch_conflict.alloc.links
            [&CommsHandle::new(fixture_switch_conflict.app_spec.id(), svc0_svc2_conn_id)]
            .as_ref()
            .unwrap();
        let svc0_svc0_switch_link_0 = conflict_path.source();
        let svc0_svc0_switch_link_1 = switch_conflict_path.source();
        // We know these two links don't conflict because they aren't the same
        // and consequently don't have the same gather/scatter endpoints. (And
        // consequently they aren't a member of the common links.)
        assert_ne!(svc0_svc0_switch_link_0, svc0_svc0_switch_link_1);
        assert!(!rsv_conflict
            .common_links(&rsv_switch_conflict)
            .contains(&svc0_svc0_switch_link_0));
        assert!(!rsv_conflict
            .common_links(&rsv_switch_conflict)
            .contains(&svc0_svc0_switch_link_1));
        let svc0_switch_rx_cycles = (svc0_tx_cycles as i64
            + fixture_conflict.sys_spec.ugn(svc0_svc0_switch_link_0))
            as usize;
        // However the links do share the crossbar and require common resources
        // for the muxing.
        let svc0_switch_id = fixture_conflict.switch_nodes[&svc0_sys_id];
        assert!(rsv_conflict
            .common_nodes(&rsv_switch_conflict)
            .contains(&svc0_switch_id));
        let svc0_switch_crossbar_latency = fixture_conflict
            .sys_spec
            .get_node(svc0_switch_id)
            .borrow()
            .into_provisioned_switch_node()
            .unwrap()
            .crossbar_latency()
            .0;
        let conflict_cycle = svc0_switch_rx_cycles + svc0_switch_crossbar_latency;
        let conflict_action = &rsv_conflict.node_table[&svc0_switch_id][&conflict_cycle];
        let switch_conflict_action =
            &rsv_switch_conflict.node_table[&svc0_switch_id][&conflict_cycle];
        assert!(conflict_action.conflicts(switch_conflict_action));
        match (conflict_action, switch_conflict_action) {
            (NodeAction::Switch(conflict_action), NodeAction::Switch(switch_conflict_action)) => {
                let (conflict_ingress, conflict_egress) =
                    conflict_action.muxes.iter().next().unwrap();
                let (switch_conflict_ingress, switch_conflict_egress) =
                    switch_conflict_action.muxes.iter().next().unwrap();
                assert_ne!(conflict_ingress, switch_conflict_ingress);
                assert_eq!(conflict_egress, switch_conflict_egress);
            }
            _ => assert!(false),
        };
        let svc0_switch_svc1_switch_link_tx_cycles = conflict_cycle + 1;
        let conflict_path_hops = fixture_conflict.alloc.links
            [&CommsHandle::new(fixture_conflict.app_spec.id(), svc0_svc2_conn_id)]
            .as_ref()
            .unwrap()
            .switch_hops()
            .drain(..)
            .collect::<HashMap<_, _>>();
        let switch_conflict_path_hops = fixture_switch_conflict.alloc.links
            [&CommsHandle::new(fixture_switch_conflict.app_spec.id(), svc0_svc2_conn_id)]
            .as_ref()
            .unwrap()
            .switch_hops()
            .drain(..)
            .collect::<HashMap<_, _>>();

        // 2. egress of svc0_switch (ingress of svc1_switch)
        //   - gathers conflict at the source of the link
        //   - scatters conflict at the sink of the link (after the logical latency)
        let svc0_switch_svc1_switch_link_id = conflict_path_hops[&svc0_svc0_switch_link_0][0];
        assert!(rsv_conflict
            .common_links(&rsv_switch_conflict)
            .contains(&svc0_switch_svc1_switch_link_id));
        assert_eq!(
            svc0_switch_svc1_switch_link_id,
            switch_conflict_path_hops[&svc0_svc0_switch_link_1][0]
        );
        let conflict_link_action = &rsv_conflict.link_table[&svc0_switch_svc1_switch_link_id]
            [&svc0_switch_svc1_switch_link_tx_cycles];
        let switch_conflict_link_action = &rsv_switch_conflict.link_table
            [&svc0_switch_svc1_switch_link_id][&svc0_switch_svc1_switch_link_tx_cycles];
        assert!(conflict_link_action.conflicts(&switch_conflict_link_action));
        match (conflict_link_action, switch_conflict_link_action) {
            (
                LinkAction {
                    gather: Some(conflict_link_action),
                    scatter: _,
                },
                LinkAction {
                    gather: Some(switch_conflict_link_action),
                    scatter: _,
                },
            ) => {
                assert_eq!(conflict_link_action.path_idx.0, 0);
                assert_eq!(switch_conflict_link_action.path_idx.0, 0);
            }
            _ => assert!(
                false,
                "link {:?} cycle {} {:#?} {:#?}",
                svc0_switch_svc1_switch_link_id,
                svc0_switch_svc1_switch_link_tx_cycles,
                conflict_link_action,
                switch_conflict_link_action
            ),
        }
        let svc0_switch_svc1_switch_link_rx_cycles = (svc0_switch_svc1_switch_link_tx_cycles as i64
            + fixture_conflict
                .sys_spec
                .ugn(svc0_switch_svc1_switch_link_id))
            as usize;
        assert!(rsv_conflict.link_table[&svc0_switch_svc1_switch_link_id]
            .contains_key(&svc0_switch_svc1_switch_link_rx_cycles));
        assert!(
            rsv_switch_conflict.link_table[&svc0_switch_svc1_switch_link_id]
                .contains_key(&svc0_switch_svc1_switch_link_rx_cycles)
        );
        let conflict_link_action = &rsv_conflict.link_table[&svc0_switch_svc1_switch_link_id]
            [&svc0_switch_svc1_switch_link_rx_cycles];
        let switch_conflict_link_action = &rsv_switch_conflict.link_table
            [&svc0_switch_svc1_switch_link_id][&svc0_switch_svc1_switch_link_rx_cycles];
        match (conflict_link_action, switch_conflict_link_action) {
            (
                LinkAction {
                    gather: _,
                    scatter: Some(conflict_link_action),
                },
                LinkAction {
                    gather: _,
                    scatter: Some(switch_conflict_link_action),
                },
            ) => {
                assert_eq!(conflict_link_action.path_idx.0, 0);
                assert_eq!(switch_conflict_link_action.path_idx.0, 0);
            }
            _ => assert!(
                false,
                "link {:?} cycle {} {:#?} {:#?}",
                svc0_switch_svc1_switch_link_id,
                svc0_switch_svc1_switch_link_rx_cycles,
                conflict_link_action,
                switch_conflict_link_action
            ),
        }
        let (_, svc1_switch_id) = fixture_conflict
            .sys_spec
            .get_link_endpoints(svc0_switch_svc1_switch_link_id);
        let svc1_switch_crossbar_latency = fixture_conflict
            .sys_spec
            .get_node(svc1_switch_id)
            .borrow()
            .into_provisioned_switch_node()
            .unwrap()
            .crossbar_latency()
            .0;
        // 3. crossbar of svc1_switch
        let svc1_switch_crossbar_cycles =
            svc0_switch_svc1_switch_link_rx_cycles + svc1_switch_crossbar_latency;
        assert!(rsv_conflict
            .common_nodes(&rsv_switch_conflict)
            .contains(&svc1_switch_id));
        match (
            &rsv_conflict.node_table[&svc1_switch_id][&svc1_switch_crossbar_cycles],
            &rsv_switch_conflict.node_table[&svc1_switch_id][&svc1_switch_crossbar_cycles],
        ) {
            (NodeAction::Switch(conflict), NodeAction::Switch(switch_conflict)) => {
                assert_eq!(conflict.muxes, switch_conflict.muxes);
            }
            _ => assert!(false),
        }
        // 4. egress of svc1_switch (ingress of svc2_switch)
        let svc1_switch_svc2_switch_link_id =
            conflict_path_hops[&svc0_switch_svc1_switch_link_id][0];
        let svc1_switch_svc2_switch_tx_cycles = svc1_switch_crossbar_cycles + 1;
        assert_eq!(
            svc1_switch_svc2_switch_link_id,
            switch_conflict_path_hops[&svc0_switch_svc1_switch_link_id][0]
        );
        assert!(rsv_conflict
            .common_links(&rsv_switch_conflict)
            .contains(&svc1_switch_svc2_switch_link_id));
        assert!(rsv_conflict.link_table[&svc1_switch_svc2_switch_link_id]
            .contains_key(&svc1_switch_svc2_switch_tx_cycles));
        assert!(
            rsv_switch_conflict.link_table[&svc1_switch_svc2_switch_link_id]
                .contains_key(&svc1_switch_svc2_switch_tx_cycles)
        );
        let conflict_link_action = &rsv_conflict.link_table[&svc1_switch_svc2_switch_link_id]
            [&svc1_switch_svc2_switch_tx_cycles];
        let switch_conflict_link_action = &rsv_switch_conflict.link_table
            [&svc1_switch_svc2_switch_link_id][&svc1_switch_svc2_switch_tx_cycles];
        match (conflict_link_action, switch_conflict_link_action) {
            (
                LinkAction {
                    gather: Some(conflict_action),
                    scatter: _,
                },
                LinkAction {
                    gather: Some(switch_conflict_action),
                    scatter: _,
                },
            ) => {
                assert_eq!(conflict_action.path_idx.0, 0);
                assert_eq!(switch_conflict_action.path_idx.0, 0);
            }
            _ => assert!(
                false,
                "link {:?} cycle {} {:#?} {:#?}",
                svc1_switch_svc2_switch_link_id,
                svc1_switch_svc2_switch_tx_cycles,
                conflict_link_action,
                switch_conflict_link_action
            ),
        }
    }

    #[test]
    fn test_conflicting_path() {
        // The conflicting path,
        //
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //    +---- | svc0_switch |
        //    |     +-------------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+     +------+
        //    |     | svc1_switch | --> | svc1 |
        //    |     |             | <-- |      |
        //    |     +-------------+     +------+
        //    |            #
        //    |            #
        //    |            v
        //    |     +-------------+
        //    +---> | svc2_switch |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let fixture = test_fixture(
            Fixture::UniFreqSwitchConflict,
            Some(StartingCycles::Uniform(0)),
        );
        // This fixture (with starting cycles 0) guarantees that application
        // path svc0 -> svc2 conflicts with svc1 -> svc2 by construction.
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc1_id = fixture.app_spec.get_node_index_by_name("svc1").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();

        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);
        let svc0_svc1_conn_id = fixture.get_app_link(&svc0_id, &svc1_id);
        let svc1_svc2_conn_id = fixture.get_app_link(&svc1_id, &svc2_id);

        let svc0_svc2_outbox = fixture.get_outbox(&svc0_svc2_conn_id);
        let svc0_svc1_outbox = fixture.get_outbox(&svc0_svc1_conn_id);
        let svc1_svc2_outbox = fixture.get_outbox(&svc1_svc2_conn_id);

        let rsv_svc0_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc2_outbox],
        );
        let rsv_svc0_svc1 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc1_outbox],
        );
        let rsv_svc1_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc1_svc2_outbox],
        );

        assert!(fixture
            .sys_spec
            .iter_links()
            .map(|link_id| { fixture.sys_spec.get_link(link_id).latency().0 })
            .all(|v| v == 1));
        assert!(fixture
            .switch_nodes
            .values()
            .map(|node_id| {
                fixture
                    .sys_spec
                    .get_node(*node_id)
                    .borrow()
                    .into_provisioned_switch_node()
                    .unwrap()
                    .crossbar_latency()
                    .0
            })
            .all(|v| v == 1));

        // svc0 -> svc2 conflicts with svc0 -> svc1, both paths have the same latency
        // to svc1_switch, and conflict for the entire MSG_SIZE duration.
        for offset in 0..=MSG_SIZE {
            if offset < MSG_SIZE {
                assert!(rsv_svc0_svc2.conflicts(&rsv_svc0_svc1, offset));
            } else {
                // translated beyond the frame count they no longer conflict
                assert!(!rsv_svc0_svc2.conflicts(&rsv_svc0_svc1, offset));
            }
        }

        // svc0 -> svc2 has a 5-cycle latency before reaching the svc1_switch
        //   - occupies svc1_switch's crossbar at cycles (5, 6, 7, 8, 9, 10, 11, 12)
        // svc1 -> svc2 has a 2-cycle latency before reading the svc1_switch
        //   - @ offset = 0, requires crossbar at cycles (2, 3, 4, 5, 6, 7, 8)
        //
        // => requires 3 extra cycles of translation (in addition to MSG_SIZE) to
        // avoid conflicts
        for offset in 0..=(MSG_SIZE + 3) {
            if offset < MSG_SIZE + 3 {
                assert!(rsv_svc0_svc2.conflicts(&rsv_svc1_svc2, offset));
            } else {
                assert!(!rsv_svc0_svc2.conflicts(&rsv_svc1_svc2, offset));
            }
        }

        assert!(!rsv_svc0_svc1.conflicts(&rsv_svc1_svc2, 0));
    }

    #[test]
    fn test_disjoint_paths() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, Some(StartingCycles::Uniform(0)));
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc1_id = fixture.app_spec.get_node_index_by_name("svc1").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();

        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);
        let svc0_svc1_conn_id = fixture.get_app_link(&svc0_id, &svc1_id);
        let svc1_svc2_conn_id = fixture.get_app_link(&svc1_id, &svc2_id);

        let svc0_svc2_outbox = fixture.get_outbox(&svc0_svc2_conn_id);
        let svc0_svc1_outbox = fixture.get_outbox(&svc0_svc1_conn_id);
        let svc1_svc2_outbox = fixture.get_outbox(&svc1_svc2_conn_id);

        let rsv_svc0_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc2_outbox],
        );
        let rsv_svc0_svc1 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc1_outbox],
        );
        let rsv_svc1_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc1_svc2_outbox],
        );

        assert!(!rsv_svc0_svc2.conflicts(&rsv_svc1_svc2, 0));
        assert!(!rsv_svc0_svc2.conflicts(&rsv_svc0_svc1, 0));
        assert!(!rsv_svc1_svc2.conflicts(&rsv_svc0_svc1, 0));
    }

    #[test]
    fn test_explicitly_merged_reservations() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, Some(StartingCycles::Uniform(0)));
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc1_id = fixture.app_spec.get_node_index_by_name("svc1").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();

        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);
        let svc0_svc1_conn_id = fixture.get_app_link(&svc0_id, &svc1_id);
        let svc1_svc2_conn_id = fixture.get_app_link(&svc1_id, &svc2_id);

        let svc0_svc2_outbox = fixture.get_outbox(&svc0_svc2_conn_id);
        let svc0_svc1_outbox = fixture.get_outbox(&svc0_svc1_conn_id);
        let svc1_svc2_outbox = fixture.get_outbox(&svc1_svc2_conn_id);

        let mut rsv = ReservationTable::new();
        let rsv_svc0_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc2_outbox],
        );
        let rsv_svc0_svc1 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc1_outbox],
        );
        let rsv_svc1_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc1_svc2_outbox],
        );
        let rsv_svc0 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc0_id),
        );
        let rsv_svc1 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc1_id),
        );
        let rsv_svc2 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc2_id),
        );

        // By construction all these individual reservations are conflict free w.r.t. one another.
        let all_rsvs = [
            &rsv_svc0_svc2,
            &rsv_svc0_svc1,
            &rsv_svc1_svc2,
            &rsv_svc0,
            &rsv_svc1,
            &rsv_svc2,
        ];
        for i in 0..all_rsvs.len() {
            for j in (i + 1)..all_rsvs.len() {
                assert!(!all_rsvs[i].conflicts(&all_rsvs[j], 0));
            }
        }
        // After each merge the aggregate should conflict with the reservation that's been merged.
        rsv.merge(&rsv_svc0_svc2, 0).unwrap();
        assert!(rsv.conflicts(&rsv_svc0_svc2, 0));

        rsv.merge(&rsv_svc0_svc1, 0).unwrap();
        assert!(rsv.conflicts(&rsv_svc0_svc1, 0));

        rsv.merge(&rsv_svc1_svc2, 0).unwrap();
        assert!(rsv.conflicts(&rsv_svc1_svc2, 0));

        rsv.merge(&rsv_svc0, 0).unwrap();
        assert!(rsv.conflicts(&rsv_svc0, 0));

        rsv.merge(&rsv_svc1, 0).unwrap();
        assert!(rsv.conflicts(&rsv_svc1, 0));

        rsv.merge(&rsv_svc2, 0).unwrap();
        assert!(rsv.conflicts(&rsv_svc2, 0));

        let mut node_tally: HashMap<NodeIndex, HashSet<usize>> = HashMap::new();
        for (node_id, node_cycles) in rsv_svc0_svc2
            .node_table
            .iter()
            .chain(rsv_svc0_svc1.node_table.iter())
            .chain(rsv_svc1_svc2.node_table.iter())
            .chain(rsv_svc0.node_table.iter())
            .chain(rsv_svc1.node_table.iter())
            .chain(rsv_svc2.node_table.iter())
        {
            if let Some(node_tally) = node_tally.get_mut(node_id) {
                node_tally.extend(node_cycles.keys());
            } else {
                node_tally.insert(
                    *node_id,
                    node_cycles.keys().cloned().collect::<HashSet<_>>(),
                );
            }
        }
        let mut link_tally: HashMap<EdgeIndex, HashSet<usize>> = HashMap::new();
        for (link_id, link_cycles) in rsv_svc0_svc2
            .link_table
            .iter()
            .chain(rsv_svc0_svc1.link_table.iter())
            .chain(rsv_svc1_svc2.link_table.iter())
            .chain(rsv_svc0.link_table.iter())
            .chain(rsv_svc1.link_table.iter())
            .chain(rsv_svc2.link_table.iter())
        {
            if let Some(link_tally) = link_tally.get_mut(link_id) {
                link_tally.extend(link_cycles.keys());
            } else {
                link_tally.insert(
                    *link_id,
                    link_cycles.keys().cloned().collect::<HashSet<_>>(),
                );
            }
        }

        // As a coarser check the aggregate reservation should contain all the
        // link & node reservations of those merged.
        assert_eq!(
            rsv.node_table.keys().collect::<HashSet<_>>(),
            node_tally.keys().collect::<HashSet<_>>()
        );
        assert_eq!(
            rsv.link_table.keys().collect::<HashSet<_>>(),
            link_tally.keys().collect::<HashSet<_>>()
        );

        // As a finer check the cycles annotated by each individual reservation
        // should be a subset of the cycles marked for the aggregate.
        for (node_id, cycles) in node_tally {
            for rsv in all_rsvs {
                if let Some(node_cycles) = rsv.node_table.get(&node_id) {
                    assert!(node_cycles.keys().all(|k| cycles.contains(k)));
                }
            }
        }
    }

    #[test]
    fn test_new_reservations() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);

        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc1_id = fixture.app_spec.get_node_index_by_name("svc1").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();

        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);
        let svc0_svc1_conn_id = fixture.get_app_link(&svc0_id, &svc1_id);
        let svc1_svc2_conn_id = fixture.get_app_link(&svc1_id, &svc2_id);

        let svc0_svc2_outbox = fixture.get_outbox(&svc0_svc2_conn_id);
        let svc0_svc1_outbox = fixture.get_outbox(&svc0_svc1_conn_id);
        let svc1_svc2_outbox = fixture.get_outbox(&svc1_svc2_conn_id);

        let rsv_svc0_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc2_outbox],
        );
        let rsv_svc0_svc1 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc1_outbox],
        );
        let rsv_svc1_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc1_svc2_outbox],
        );
        let rsv_svc0 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc0_id),
        );
        let rsv_svc1 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc1_id),
        );
        let rsv_svc2 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc2_id),
        );
        let ref_reservations = [
            &rsv_svc0_svc2,
            &rsv_svc0_svc1,
            &rsv_svc1_svc2,
            &rsv_svc0,
            &rsv_svc1,
            &rsv_svc2,
        ];
        let (mut reservations, mut comms_reservations) = ReservationTable::new_reservations(
            &fixture.app_spec,
            &fixture.sys_spec,
            &fixture.alloc,
        );
        reservations.append(&mut comms_reservations);
        assert_eq!(ref_reservations.len(), reservations.len());
        for ref_rsv in ref_reservations {
            assert!(reservations
                .iter()
                .find(|rsv| {
                    rsv.node_table == ref_rsv.node_table && rsv.link_table == ref_rsv.link_table
                })
                .is_some())
        }
    }

    #[test]
    fn test_concat_no_conflict() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);
        // Since there are no conflicts, the concat schedule should be
        // equivalent to the reservations being merged with offset 0 in any
        // order.
        let (mut rsv, mut comms_rsv) = ReservationTable::new_reservations(
            &fixture.app_spec,
            &fixture.sys_spec,
            &fixture.alloc,
        );
        rsv.append(&mut comms_rsv);
        let mut accum_rsv = ReservationTable::new();
        rsv.iter()
            .fold(&mut accum_rsv, |accum, rsv| accum.merge(rsv, 0).unwrap());
        let mut concat_rsv = ReservationTable::new();
        rsv.iter().fold(&mut concat_rsv, |accum, rsv| {
            accum.concat(rsv, &fixture.sys_spec).unwrap()
        });
        assert_eq!(accum_rsv, concat_rsv);
    }

    #[test]
    fn test_concat_scheduler_no_conflict() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);

        let [concat_comp_rsv, concat_comms_rsv] = concat_scheduler::<BUFFERING_DOUBLE>(
            &[&fixture.app_spec],
            &fixture.sys_spec,
            &fixture.alloc,
        )
        .unwrap();

        let mut ref_comp_rsv = ReservationTable::new();
        let mut ref_comms_rsv = ReservationTable::new();
        let (comp_rsvs, comms_rsvs) = ReservationTable::new_reservations(
            &fixture.app_spec,
            &fixture.sys_spec,
            &fixture.alloc,
        );
        for rsv in &comp_rsvs {
            ref_comp_rsv.concat(rsv, &fixture.sys_spec).unwrap();
        }
        for rsv in &comms_rsvs {
            ref_comms_rsv.concat(rsv, &fixture.sys_spec).unwrap();
        }
        assert_eq!(concat_comp_rsv, ref_comp_rsv);
        assert_eq!(concat_comms_rsv.paths.len(), 3);
        assert_eq!(concat_comms_rsv.batching.len(), 3);
    }

    #[test]
    fn test_reservation_resources_must_be_non_empty() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);
        let (comp_rsvs, comms_rsvs) = ReservationTable::new_reservations(
            &fixture.app_spec,
            &fixture.sys_spec,
            &fixture.alloc,
        );
        for rsv in &comp_rsvs {
            assert!(rsv.node_table.values().all(|v| !v.is_empty()));
        }
        for rsv in &comms_rsvs {
            assert!(rsv.link_table.values().all(|v| !v.is_empty()));
        }
    }

    #[test]
    fn test_concat_scheduler_conflict() {
        let fixture = test_fixture(Fixture::UniFreqConflict, Some(StartingCycles::Uniform(0)));

        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc1_id = fixture.app_spec.get_node_index_by_name("svc1").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();

        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);
        let svc0_svc1_conn_id = fixture.get_app_link(&svc0_id, &svc1_id);
        let svc1_svc2_conn_id = fixture.get_app_link(&svc1_id, &svc2_id);

        let svc0_svc2_outbox = fixture.get_outbox(&svc0_svc2_conn_id);
        let svc0_svc1_outbox = fixture.get_outbox(&svc0_svc1_conn_id);
        let svc1_svc2_outbox = fixture.get_outbox(&svc1_svc2_conn_id);

        let rsv_svc0_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc2_outbox],
        );
        let rsv_svc0_svc1 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc0_svc1_outbox],
        );
        let rsv_svc1_svc2 = ReservationTable::new_comms_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &[&svc1_svc2_outbox],
        );
        let rsv_svc0 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc0_id),
        );
        let rsv_svc1 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc1_id),
        );
        let rsv_svc2 = ReservationTable::new_compute_reservation(
            &fixture.sys_spec,
            &fixture.alloc,
            &ServiceHandle::new(fixture.app_spec.id(), svc2_id),
        );
        let mut concat_rsv = ReservationTable::new();

        // Required assumptions for assertions.
        assert!(fixture
            .sys_spec
            .iter_links()
            .all(|link_id| { fixture.sys_spec.get_link(link_id).latency().0 == 1 }));
        assert!(fixture.switch_nodes.values().all(|switch_id| {
            fixture
                .sys_spec
                .get_node(*switch_id)
                .borrow()
                .into_provisioned_switch_node()
                .unwrap()
                .crossbar_latency()
                .0
                == 1
        }));
        assert_eq!(MSG_SIZE / FRAME_SIZE, 8);

        // We know none of the compute reservations conflict, so concat should
        // put them at offsets of zero.
        concat_rsv.concat(&rsv_svc0, &fixture.sys_spec).unwrap();
        assert!(concat_rsv.conflicts(&rsv_svc0, 0));

        concat_rsv.concat(&rsv_svc1, &fixture.sys_spec).unwrap();
        assert!(concat_rsv.conflicts(&rsv_svc1, 0));

        concat_rsv.concat(&rsv_svc2, &fixture.sys_spec).unwrap();
        assert!(concat_rsv.conflicts(&rsv_svc2, 0));

        assert_eq!(rsv_svc0_svc2.common_links(&concat_rsv), HashSet::new());
        assert_eq!(rsv_svc0_svc2.common_nodes(&concat_rsv), HashSet::new());
        // svc0 -> svc2 can be scheduled at offset 0 since its the first path to
        // be scheduled.
        concat_rsv
            .concat(&rsv_svc0_svc2, &fixture.sys_spec)
            .unwrap();
        assert!(concat_rsv.conflicts(&rsv_svc0_svc2, 0));

        // svc0 -> svc2 conflicts with svc1 -> svc2
        //
        // app path: svc0 -> svc2
        //
        // svc0 -> svc0_switch{gather}         : 0-7
        // svc0 -> svc0_switch{scatter}        : 1-8
        // svc0_switch{crossbar}               : 2-9
        // svc0_switch -> svc_switch1{gather}  : 3-10
        // svc0_switch -> svc_switch1{scatter} : 4-11
        // svc1_switch{crossbar}               : 5-12  <==
        // svc1_switch -> svc2_switch{gather}  : 6-13
        // svc1_switch -> svc2_switch{scatter} : 7-14
        // svc2_switch{crossbar}               : 8-15
        // svc2_switch -> svc2{gather}         : 9-16
        // svc2_switch -> svc2{scatter}        : 10-17
        //
        // app path: svc1 -> svc2 @ offset = 3 + MSG_SIZE = 11
        //
        // svc1 -> svc1_switch{gather}         : 11-18
        // svc1 -> svc1_switch{scatter}        : 12-19
        // svc1_switch{crossbar}               : 13-20 <==
        // svc1_switch -> svc2_switch{gather}  : 14-21
        // svc1_switch -> svc2_switch{scatter} : 15-22
        // svc2_switch{crossbar}               : 16-23
        // svc2_switch -> svc2{gather}         : 17-24
        // svc2_switch -> svc2{scatter}        : 18-25
        //
        // at offset of 11 svc1_switch becomes conflict free (13 > 12)

        for offset in 0..(3 + MSG_SIZE) {
            assert!(concat_rsv.conflicts(&rsv_svc1_svc2, offset));
        }
        assert!(!concat_rsv.conflicts(&rsv_svc1_svc2, 3 + MSG_SIZE));
        concat_rsv
            .concat(&rsv_svc1_svc2, &fixture.sys_spec)
            .unwrap();
        assert!(concat_rsv.conflicts(&rsv_svc1_svc2, 3 + MSG_SIZE));

        // svc0 -> svc2 conflicts with svc0 -> svc1,
        //
        // But svc1_switch doesn't conflict in these two paths, they're
        // disjoint!
        //
        // Where it conflicts is svc0 -> svc0_switch, which can be
        // avoided by an offset of MSG_SIZE.
        //
        // app path: svc0 -> svc1 @ offset = 8
        //
        // svc0 -> svc0_switch{gather}         : 8-15
        // svc0 -> svc0_switch{scatter}        : 9-16
        // svc0_switch{crossbar}               : 10-17
        // svc0_switch -> svc_switch1{gather}  : 11-18
        // svc0_switch -> svc_switch1{scatter} : 12-19
        // svc1_switch{crossbar}               : 13-20
        // svc1_switch -> svc1{gather}         : 14-21
        // svc1_switch -> svc1{scatter}        : 15-22
        for offset in 0..MSG_SIZE {
            assert!(concat_rsv.conflicts(&rsv_svc0_svc1, offset));
        }
        assert!(!concat_rsv.conflicts(&rsv_svc0_svc1, MSG_SIZE));
        concat_rsv
            .concat(&rsv_svc0_svc1, &fixture.sys_spec)
            .unwrap();
        assert!(concat_rsv.conflicts(&rsv_svc0_svc1, MSG_SIZE));

        assert_eq!(concat_rsv.paths.len(), 3);

        // Check that svc1_switch has 2 ingress/egress edges due
        // to merger of app paths svc0 -> svc2, svc0 -> svc1 at
        // the switch.
        let svc1_sys_id = fixture.alloc.nodes[&ServiceHandle::new(fixture.app_spec.id(), svc1_id)];
        let svc1_switch_id = fixture.switch_nodes[&svc1_sys_id];
        let action = &concat_rsv.node_table[&svc1_switch_id][&13];
        match action {
            NodeAction::Switch(rsv) => {
                // 2 ingress edges
                assert_eq!(rsv.muxes.keys().count(), 2);
                // each ingress has 1 egress
                assert!(rsv.muxes.values().all(|v| v.len() == 1));
                // egresses are disjoint
                assert_eq!(
                    rsv.muxes.values().flatten().collect::<HashSet<_>>().len(),
                    2
                );
            }
            _ => assert!(false),
        }
    }

    #[test]
    fn test_get_link_calendar() {
        //          +-------------+
        //          |    svc0     |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //    ##### | svc0_switch |
        //    #     +-------------+
        //    #            |
        //    #            |
        //    #            v
        //    #     +-------------+     +------+
        //    #     | svc1_switch | --> | svc1 |
        //    #     |             | <-- |      |
        //    #     +-------------+     +------+
        //    #            |
        //    #            |
        //    #            v
        //    #     +-------------+
        //    ####> | svc2_switch |
        //          +-------------+
        //            |         #
        //            |         #
        //            v         v
        //          +-------------+
        //          |    svc2     |
        //          +-------------+
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);
        let [_, comms_rsv] = concat_scheduler::<BUFFERING_DOUBLE>(
            &[&fixture.app_spec],
            &fixture.sys_spec,
            &fixture.alloc,
        )
        .unwrap();
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();
        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);
        let path = fixture.alloc.links[&CommsHandle::new(fixture.app_spec.id(), svc0_svc2_conn_id)]
            .as_ref()
            .unwrap();
        let outbox = fixture.get_outbox(&svc0_svc2_conn_id);
        let path_hops = path.switch_hops().drain(..).collect::<HashMap<_, _>>();
        let svc0_svc0_switch_link_id = path.source();
        let outbox_address = outbox
            .mapped_endpoint
            .as_ref()
            .unwrap()
            .base_address
            .unwrap() as u32;

        fn flatten<T: Clone>(v: Vec<Vec<T>>) -> Vec<T> {
            v.iter().flatten().cloned().collect()
        }
        let latencies = path.path_latencies(&fixture.sys_spec);
        let rx_cycle =
            |tx_cycle: usize, link_id: &EdgeIndex| (tx_cycle as i64 + latencies[link_id]) as usize;
        assert!(fixture.switch_nodes.values().all(|switch_id| fixture
            .sys_spec
            .get_node(*switch_id)
            .borrow()
            .into_provisioned_switch_node()
            .unwrap()
            .crossbar_latency()
            .0
            == 1));
        // svc0 -> svc0_switch
        let (svc0_start, svc0_switch_start) =
            fixture.link_endpoint_start_times(&svc0_svc0_switch_link_id);
        let svc0_svc0_switch_rx_cycle = rx_cycle(svc0_start, &svc0_svc0_switch_link_id);
        assert_eq!(
            comms_rsv
                .link_calendar(&svc0_svc0_switch_link_id, &fixture.sys_spec)
                .unwrap(),
            (
                vec![CalendarEntry::new(Some(outbox_address), MSG_SIZE)],
                flatten(vec![
                    vec![CalendarEntry::new(
                        None,
                        svc0_svc0_switch_rx_cycle - svc0_switch_start
                    )],
                    vec![CalendarEntry::new(Some(0), 1); MSG_SIZE]
                ])
            )
        );
        // svc0_switch -> svc2_switch
        let svc0_switch_svc2_switch_link_id = path_hops[&svc0_svc0_switch_link_id][0];
        let svc0_switch_svc2_switch_rx_cycle =
            rx_cycle(svc0_start, &svc0_switch_svc2_switch_link_id);
        let (_, svc2_switch_start) =
            fixture.link_endpoint_start_times(&svc0_switch_svc2_switch_link_id);
        assert_eq!(
            comms_rsv
                .link_calendar(&svc0_switch_svc2_switch_link_id, &fixture.sys_spec)
                .unwrap(),
            (
                flatten(vec![
                    vec![CalendarEntry::new(
                        None,
                        2 + (svc0_svc0_switch_rx_cycle - svc0_switch_start)
                    )],
                    vec![CalendarEntry::new(Some(0), 1); MSG_SIZE]
                ]),
                flatten(vec![
                    vec![CalendarEntry::new(
                        None,
                        svc0_switch_svc2_switch_rx_cycle - svc2_switch_start
                    )],
                    vec![CalendarEntry::new(Some(0), 1); MSG_SIZE]
                ])
            )
        );
        // svc2_switch -> svc2
        let svc2_switch_svc2_link_id = path_hops[&svc0_switch_svc2_switch_link_id][0];
        let svc2_switch_svc2_rx_cycle = rx_cycle(svc0_start, &svc2_switch_svc2_link_id);
        let (_, svc2_sys_id) = fixture
            .sys_spec
            .get_link_endpoints(svc2_switch_svc2_link_id);
        let (_, svc2_start) = fixture.link_endpoint_start_times(&svc2_switch_svc2_link_id);
        let inbox = fixture
            .sys_spec
            .get_node(svc2_sys_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .get_mailbox()
            .unwrap()
            .inboxes
            .iter()
            .find(|comms_attrs| {
                comms_attrs.connection_id
                    == CommsHandle::new(fixture.app_spec.id(), svc0_svc2_conn_id)
            })
            .unwrap()
            .clone();
        let inbox_address = inbox.mapped_endpoint.unwrap().base_address.unwrap() as u32;
        assert_eq!(
            comms_rsv
                .link_calendar(&svc2_switch_svc2_link_id, &fixture.sys_spec)
                .unwrap(),
            (
                flatten(vec![
                    vec![CalendarEntry::new(
                        None,
                        2 + (svc0_switch_svc2_switch_rx_cycle - svc2_switch_start)
                    )],
                    vec![CalendarEntry::new(Some(0), 1); MSG_SIZE]
                ]),
                flatten(vec![
                    vec![CalendarEntry::new(
                        None,
                        svc2_switch_svc2_rx_cycle - svc2_start
                    )],
                    vec![CalendarEntry::new(Some(inbox_address), 8)]
                ])
            )
        );
    }

    #[test]
    fn test_get_switch_calendar() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, Some(StartingCycles::Uniform(0)));

        let [_, concat_comms_rsv] = concat_scheduler::<BUFFERING_DOUBLE>(
            &[&fixture.app_spec],
            &fixture.sys_spec,
            &fixture.alloc,
        )
        .unwrap();
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc1_id = fixture.app_spec.get_node_index_by_name("svc1").unwrap();
        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();
        let svc0_svc1_conn_id = fixture.get_app_link(&svc0_id, &svc1_id);
        let svc0_svc2_conn_id = fixture.get_app_link(&svc0_id, &svc2_id);

        let svc0_svc2_path = &fixture.alloc.links
            [&CommsHandle::new(fixture.app_spec.id(), svc0_svc2_conn_id)]
            .as_ref()
            .unwrap();
        let svc0_svc1_path = &fixture.alloc.links
            [&CommsHandle::new(fixture.app_spec.id(), svc0_svc1_conn_id)]
            .as_ref()
            .unwrap();

        let svc0_svc2_path_hops = svc0_svc2_path
            .switch_hops()
            .drain(..)
            .collect::<HashMap<_, _>>();
        let svc0_svc1_path_hops = svc0_svc1_path
            .switch_hops()
            .drain(..)
            .collect::<HashMap<_, _>>();

        // app conn: svc0 -> svc2
        // svc0_switch ingress and egress
        let svc0_svc0_switch_link0_id = svc0_svc2_path.source();
        let svc0_switch_svc2_switch_link_id = svc0_svc2_path_hops[&svc0_svc0_switch_link0_id][0];

        // app conn: svc0 -> svc1
        // svc0_switch ingress and egress
        let svc0_svc0_switch_link1_id = svc0_svc1_path.source();
        let svc0_switch_svc1_switch_link_id = svc0_svc1_path_hops[&svc0_svc0_switch_link1_id][0];

        // output port -> input port
        let mut switch_mux = HashMap::<usize, usize>::new();
        switch_mux.insert(
            fixture
                .sys_spec
                .get_link(svc0_switch_svc2_switch_link_id)
                .src_port()
                .into(),
            fixture
                .sys_spec
                .get_link(svc0_svc0_switch_link0_id)
                .dst_port()
                .into(),
        );
        switch_mux.insert(
            fixture
                .sys_spec
                .get_link(svc0_switch_svc1_switch_link_id)
                .src_port()
                .into(),
            fixture
                .sys_spec
                .get_link(svc0_svc0_switch_link1_id)
                .dst_port()
                .into(),
        );
        assert_eq!(switch_mux.keys().len(), 2);
        let mut switch_mux_keys = switch_mux.keys().cloned().collect::<Vec<_>>();
        let mut switch_mux_values = switch_mux.values().cloned().collect::<Vec<_>>();
        switch_mux_keys.sort();
        switch_mux_values.sort();
        assert_eq!(switch_mux_keys, vec![0, 1]);
        assert_eq!(switch_mux_values, vec![0, 1]);
        let mux_function = vec![switch_mux[&0] as u32, switch_mux[&1] as u32];

        assert!(fixture
            .sys_spec
            .iter_links()
            .all(|link_id| { fixture.sys_spec.get_link(link_id).latency().0 == 1 }));
        assert!(fixture.switch_nodes.values().all(|node_id| {
            fixture
                .sys_spec
                .get_node(*node_id)
                .borrow()
                .into_provisioned_switch_node()
                .unwrap()
                .crossbar_latency()
                .0
                == 1
        }));

        let ref_calendar = vec![
            CrossbarCalendarEntry::new(None, 2),
            CrossbarCalendarEntry::new(Some(mux_function), MSG_SIZE),
        ];

        let svc0_switch = fixture
            .sys_spec
            .get_node_index_by_name("svc0_switch")
            .unwrap();
        let svc0_switch_calendar = concat_comms_rsv
            .switch_calendar(&svc0_switch, &fixture.sys_spec)
            .unwrap();
        assert_eq!(svc0_switch_calendar, ref_calendar);
    }

    #[test]
    fn test_get_run_calendar() {
        let fixture = test_fixture(Fixture::UniFreqNoConflict, None);
        let [concat_rsv, _] = concat_scheduler::<BUFFERING_DOUBLE>(
            &[&fixture.app_spec],
            &fixture.sys_spec,
            &fixture.alloc,
        )
        .unwrap();
        let svc0_id = fixture.app_spec.get_node_index_by_name("svc0").unwrap();
        let svc0_sys_id = fixture.alloc.nodes[&ServiceHandle::new(fixture.app_spec.id(), svc0_id)];
        assert_eq!(SVC0_COMPUTE_CYCLES, 1);
        assert_eq!(
            concat_rsv
                .node_calendar(&svc0_sys_id, &fixture.sys_spec)
                .unwrap(),
            vec![NodeCalendarEntry::new(
                Some(ServiceHandle::new(fixture.app_spec.id(), svc0_id)),
                SVC0_COMPUTE_CYCLES
            )],
        );

        let svc1_id = fixture.app_spec.get_node_index_by_name("svc1").unwrap();
        let svc1_sys_id = fixture.alloc.nodes[&ServiceHandle::new(fixture.app_spec.id(), svc1_id)];
        assert_eq!(
            concat_rsv
                .node_calendar(&svc1_sys_id, &fixture.sys_spec)
                .unwrap(),
            vec![NodeCalendarEntry::new(
                Some(ServiceHandle::new(fixture.app_spec.id(), svc1_id)),
                SVC1_COMPUTE_CYCLES
            )],
        );

        let svc2_id = fixture.app_spec.get_node_index_by_name("svc2").unwrap();
        let svc2_sys_id = fixture.alloc.nodes[&ServiceHandle::new(fixture.app_spec.id(), svc2_id)];
        assert_eq!(
            concat_rsv
                .node_calendar(&svc2_sys_id, &fixture.sys_spec)
                .unwrap(),
            vec![NodeCalendarEntry::new(
                Some(ServiceHandle::new(fixture.app_spec.id(), svc2_id)),
                SVC2_COMPUTE_CYCLES
            )],
        );
    }
}
