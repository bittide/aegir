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

//! A custom traversal of the system toplogy, such that the frames are properly aligned.

use super::*;
use crate::calendar::Buffering;
use crate::specs::ApplicationNode;
use itertools::Itertools;
use petgraph::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct MetacycleVisitor {
    /// store the indices of the nodes in the traversal order.
    ///
    /// Since the graph (topology) does not change, the order may be
    /// computed only once, at initialization time.
    /// Thus, the iterator can be reset every time we start a new cycle.
    node_serialization: Vec<NodeIndex>,

    /// the state of the traversal is a pointer into the node_serialization vector.
    current_ptr: usize,
}

impl MetacycleVisitor {
    /// all of the nodes in a system are logically concurrent (assuming the
    /// existence of appropriate hardware, each node might be assigned
    /// dedicated compute and hence all nodes could execute in parallel); to
    /// model this within a Rust program we need to find a serialization
    /// that preserves the system constraints, most importantly the
    /// coherence of link frame data -- linked nodes need to cycle in a
    /// sufficiently aligned fashion to avoid corrupting the link frame data
    /// (by having the tx side overrun the rx side, or vice versa)
    ///
    /// algorithm overview:
    ///
    /// each node needs to step for a total of (local frequency / root
    /// frequency) cycles; in a greedy manner find nodes that both have
    /// steps remaining and who also do not have lagging neighbors; lagging
    /// is determined by looking at the pairwise GCD (freq_gcd) for each
    /// linked neighbor; the local frequency divided by the shared freq_gcd
    /// for any given pair of neighbors should never exceed unit difference
    /// (doing so would imply possible frame data access overrun on their
    /// shared link)
    fn serialize_nodes<
        const B: Buffering,
        NS: NodeSpec<B> + ApplicationNode,
        LS: LinkSpec + FramingLinkTrait,
    >(
        graph: &Graph<Rc<RefCell<NS>>, LS>,
    ) -> Vec<NodeIndex> {
        // nodes cannot make more progress than what their links to their neighbors allow,
        // specifically the ratio of their frequency to the shared GCD defines one unit of
        // communication progress and nodes cannot differ in their overall progress with their
        // neighbors by more than one such unit (doing so would violate the balance of reading and
        // writing to the shared link); this function calcules how many such units of progress have
        // accrued for the target
        fn relative_progress<const B: Buffering, NS: NodeSpec<B>, LS: LinkSpec>(
            graph: &Graph<Rc<RefCell<NS>>, LS>,
            progress: &[usize],
            target_node_idx: NodeIndex,
            neighbor_frequency_gcd: FrequencyFactor,
        ) -> usize {
            let target_progress = progress[target_node_idx.index()];
            let relative_run = graph
                .node_weight(target_node_idx)
                .unwrap()
                .borrow()
                .into_application_node()
                .unwrap()
                .rate_of_service()
                .0
                / neighbor_frequency_gcd.0;
            let large_steps = target_progress / relative_run;
            let remaining_small_steps = relative_run - (target_progress % relative_run);
            log::trace!(
                "target {} progress {} rel_run {} large_steps {} rem_small_steps {}",
                target_node_idx.index(),
                target_progress,
                relative_run,
                large_steps,
                remaining_small_steps
            );
            large_steps
        }
        // return true if stepping the target node would bring it too far ahead of its neighbors
        fn has_lagging_neighbors<const B: Buffering, NS: NodeSpec<B>, LS: LinkSpec>(
            graph: &Graph<Rc<RefCell<NS>>, LS>,
            progress: &[usize],
            target_node_idx: NodeIndex,
        ) -> bool {
            let target_node = graph.node_weight(target_node_idx).unwrap();
            log::trace!(
                "neighbors {:?}",
                graph
                    .neighbors_undirected(target_node_idx)
                    .unique()
                    .map(|n| n.index())
                    .collect::<Vec<usize>>()
            );

            let target_frequency = target_node
                .borrow()
                .into_application_node()
                .unwrap()
                .rate_of_service();
            graph
                .neighbors_undirected(target_node_idx)
                .unique()
                .any(|neighbor| {
                    let neighbor_node = graph.node_weight(neighbor).unwrap().borrow();
                    let neighbor_frequency = neighbor_node
                        .into_application_node()
                        .unwrap()
                        .rate_of_service();
                    let freq_gcd = FrequencyFactor(num::integer::gcd(
                        target_frequency.0,
                        neighbor_frequency.0,
                    ));

                    let target_large_steps =
                        relative_progress(graph, progress, target_node_idx, freq_gcd);
                    let neighbor_large_steps =
                        relative_progress(graph, progress, neighbor, freq_gcd);
                    assert!(
                        (neighbor_large_steps as i32 - target_large_steps as i32).abs() <= 1,
                        "linked nodes cycle alignment violated ({} and {})",
                        neighbor_large_steps,
                        target_large_steps
                    );
                    neighbor_large_steps < target_large_steps
                })
        }

        // return the next node with unfinished cycles and no lagging neighbors
        fn next_pending_node_idx<const B: Buffering, NS: NodeSpec<B>, LS: LinkSpec>(
            graph: &Graph<Rc<RefCell<NS>>, LS>,
            progress: &[usize],
        ) -> NodeIndex {
            graph
                .node_indices()
                .find(|&node_idx| {
                    let node = graph.node_weight(node_idx).unwrap().borrow();
                    log::trace!(
                        "consider node {} freq {:?}",
                        node_idx.index(),
                        node.into_application_node().unwrap().rate_of_service()
                    );
                    progress[node_idx.index()]
                        < node.into_application_node().unwrap().rate_of_service().0
                        && !has_lagging_neighbors(graph, progress, node_idx)
                })
                .expect("no pending node could be found (but one should exist)")
        }

        // TODO(cascaval): check that the frequencies have been normalized.
        let mut progress: Vec<usize> = vec![0; graph.node_count()];
        let mut remaining_cycles = 0;
        for node_idx in graph.node_indices() {
            remaining_cycles += graph
                .node_weight(node_idx)
                .unwrap()
                .borrow()
                .rate_of_service()
                .0;
        }
        let mut result: Vec<NodeIndex> = Vec::new();
        while remaining_cycles > 0 {
            log::trace!(
                "selecting next node -- remaining local cycles: {}, progress: {:?}",
                remaining_cycles,
                progress
            );
            let target_node_idx = next_pending_node_idx(graph, &progress);
            result.push(target_node_idx);
            progress[target_node_idx.index()] += 1;
            remaining_cycles -= 1;
        }
        result
    }

    pub fn new<
        const B: Buffering,
        NS: NodeSpec<B> + ApplicationNode,
        LS: LinkSpec + FramingLinkTrait,
    >(
        graph: &Graph<Rc<RefCell<NS>>, LS>,
    ) -> Self {
        let node_serialization = Self::serialize_nodes(graph);
        Self {
            node_serialization,
            current_ptr: 0,
        }
    }

    /* TODO(cascaval): to be used when we move the simulation into the SystemSpec.
    fn empty() -> Self {
        Self {
            node_serialization: Vec::new(),
            current_ptr: 0,
        }
    }

    fn is_empty(&self) -> bool {
        self.node_serialization.len() == 0
    }
    */

    pub fn reset(&mut self) {
        self.current_ptr = 0;
    }

    /// return the index of the next node to be traversed, or None if we are
    /// at the end of the traversal.
    pub fn next(&mut self) -> Option<NodeIndex> {
        let current = self.current_ptr;
        self.current_ptr += 1;
        if current < self.node_serialization.len() {
            Some(self.node_serialization[current])
        } else {
            None
        }
    }
}
