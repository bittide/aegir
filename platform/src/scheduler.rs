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

use std::cmp::max;
use std::collections::HashMap;
use std::rc::Rc;

use crate::app::ServiceHandle;
use crate::calendar::CrossbarCalendarEntry;
use crate::calendar::{CrossbarCalendar, BUFFERING_DOUBLE};
use crate::hw::config::SwitchConfiguration;
use crate::hw::{ComputeNode, Node, SwitchNode};
use crate::scheduler::alloc::compute_batch_size;
use crate::scheduler::path::Path;
use crate::specs::Frequency;
use crate::specs::ProvisionedNode;
use crate::Buffering;
use crate::FrameSize;
use crate::{hw, Latency};
use crate::{Application, Error, HardwareSpec, Port, PortProperties};
use crate::{LinkConfiguration, NodeConfiguration};
use crate::{LinkSpec, NodeSpec};
use petgraph::prelude::*;

mod alloc;
mod path;
mod reservation;
mod sched;

pub use crate::app::CommsHandle;
pub use crate::scheduler::alloc::PathBatching;
pub use crate::scheduler::alloc::SystemAllocation;
pub use crate::scheduler::sched::Schedule;

#[derive(Clone, Debug)]
pub enum RandomAllocation {
    /// Assigns at most one service to any compute node.
    NodesOneToOne,
    /// Assigns any number of service nodes to compute nodes.
    NodesAny,
}

#[derive(Clone, Debug)]
pub enum AllocationPolicy {
    /// `OneToOne` allocation maps an application graph to an isomorphic system
    /// topology. An isomorphic HW topology implies,
    /// - 1:1 service node to compute node mappings
    /// - 1:1 connection to link mappings
    /// - NOT 1:1 application messages to HW frames mappings.
    ///    - we want non-trivial metacycles
    ///    - we want non-trivial calendar programs
    ///    - we want non-trivial number of frames to exercise batching
    ///
    /// In summary, a 1:1 mapping is only intended to make trivial the concept
    /// of embedding an application graph to a HW topology. If application
    /// message sizes are preserved and calendars are "send one frame" then one
    /// could run the software system simulation instead, there's no benefit to
    /// performing a HW simulation.
    ///
    /// The 1:1 mapping is essentially used for testing. We do not expect that
    /// this will be useful in real scenarios!
    OneToOne(MappingConfiguration1x1),

    /// Alternative adaptation of the `OneToOne` allocation that exercises
    /// switches and networking. In this model each service node is mapped to a
    /// node/switch pair. The switches are then connected as prescribed by the
    /// application topology. E.g., Given the application,
    ///
    ///  +----+          +----+
    ///  | s0 |--------->| s1 |
    ///  |    |<---------|    |
    ///  +----+          +----+
    ///
    /// An equivalent hardware topology is created as such,
    ///
    ///  +----+          +----+
    ///  | X0 |--------->| X1 |
    ///  |    |<---------|    |
    ///  +----+          +----+
    ///   ^  |            ^  |
    ///   |  v            |  v
    ///  +----+          +----+
    ///  | c0 |          | c1 |
    ///  |    |          |    |
    ///  +----+          +----+
    ///
    /// where service node s0 is mapped to compute node c0, and likewise s1
    /// is mapped to c1. For each service node s(i) a corresponding switch
    /// X(i) is created in the HW topology. These switches are then connected
    /// together in the same topology as the application network, which guarantees
    /// conflict free routing of frames.
    ///
    /// The motivation of this 1:1 mapping topology is to enable testing of
    /// networking and switches in the same way that the `OneToOne` topology enables
    /// testing of directly connected service nodes. The same type of isomorphisms
    /// are assumed as in the `OneToOne` mapping.
    ///
    /// More concretely, given the application graph A = (S, C),
    ///  - S is the set of service nodes s.t., s(i) in S
    ///  - C is the set of connections s.t. c(i, j) in S
    ///  - src(c(i,j)) = i
    ///  - dst(c(i,j)) = j
    ///
    /// We create the HW topology G = (N, L)
    /// - N is the set of compute c(i) and switch nodes X(i), s.t., c(i), X(i) \in N
    /// - L is the set of links l(n(i), n(j)), where n could be either a compute node (c)
    ///   or a switch node (X)
    /// - N = { c(i), X(i) | for all s(i) in S }
    /// - L = { l(c(i), X(i)) | for all c(i, j) for all c(i) } U { l(X(i), X(j)) | for all c(i, j) for all c(i) }
    OneToOneNetwork(MappingConfiguration1x1Network),

    /// Maps at most one service per compute node in a random manner. Places no
    /// requirements on how routing is used by the mapping.
    Random(RandomAllocation),

    ///
    /// `FirstFit` allocation is a simple policy, whereby, given a set of
    /// application requirements, allocates the first physical node that
    /// meets the requirements.
    FirstFit,

    /// `BestFit` allocation requires searching the system graph to find an
    /// assignment that minimizes application level metrics (e.g., latency
    /// of communication and computation).
    BestFit,

    Priority,
    Symbiotic,
    PowerEfficient,
    // and ... creativity is the limit!
}

pub trait AllocateTrait {
    fn allocate(
        &self,
        app_specs: &[&Application],
        policy: &AllocationPolicy,
    ) -> Result<SystemAllocation, Error>;
}

impl AllocateTrait for HardwareSpec {
    fn allocate(
        &self,
        app_specs: &[&Application],
        policy: &AllocationPolicy,
    ) -> Result<SystemAllocation, Error> {
        match policy {
            // One to One mappings are prescriptively scheduled and only support
            // double-buffering configurations.
            AllocationPolicy::OneToOne(cfg) => {
                if app_specs.len() != 1 {
                    log::error!("Can not allocate multiple applications in a 1x1 setting.");
                    return Err(Error::InvalidAllocation);
                }
                let app_spec = &app_specs[0];
                alloc::alloc_1x1(app_spec, self, cfg)
            }
            AllocationPolicy::OneToOneNetwork(cfg) => {
                if app_specs.len() != 1 {
                    log::error!("Can not allocate multiple applications in a 1x1 setting.");
                    return Err(Error::InvalidAllocation);
                }
                let app_spec = &app_specs[0];
                alloc::alloc_1x1_network(app_spec, self, cfg)
            }
            // Virtualized variants are reservation-table-scheduled and we
            // currently only support double-buffering configurations.
            AllocationPolicy::Random(random_type) => {
                alloc::alloc_random::<BUFFERING_DOUBLE>(app_specs, self, random_type)
            }
            _ => unimplemented!(),
        }
    }
}

pub trait ScheduleTrait<const BUFFERING: Buffering> {
    fn schedule(
        &self,
        app_spec: &[&Application],
        policy: &AllocationPolicy,
        allocation: &SystemAllocation,
    ) -> Result<Schedule<BUFFERING>, Error>;
}

impl ScheduleTrait<{ BUFFERING_DOUBLE }> for HardwareSpec {
    fn schedule(
        &self,
        app_spec: &[&Application],
        policy: &AllocationPolicy,
        allocation: &SystemAllocation,
    ) -> Result<Schedule<{ BUFFERING_DOUBLE }>, Error> {
        match policy {
            AllocationPolicy::OneToOne(_) | AllocationPolicy::OneToOneNetwork(_) => {
                if app_spec.len() != 1 {
                    log::error!("1x1 mappings do not support multiple applications.");
                    return Err(Error::InvalidSchedule);
                }
                let app_spec = &app_spec[0];
                let system_wide_period = time_physical_system_1x1(app_spec, self, allocation);
                // generate calendars for links
                let mut sched = Schedule::new();
                return sched
                    .generate_calendars_1x1(self, app_spec, allocation, policy, system_wide_period)
                    .map(|_| sched);
            }
            AllocationPolicy::Random(_) => {
                let rsv_tables = reservation::concat_scheduler(app_spec, self, allocation)?;
                let mut sched = Schedule::new();
                sched.generate_calendars(&rsv_tables, self)?;
                return Ok(sched);
            }
            _ => unimplemented!("Scheduling unsupported for the provided policy."),
        }
    }
}

/// Configuration for 1x1 lowering of application graph to a HW topology. Characteristics are
/// set globally (as opposed to specifically to any component or service).
#[derive(Clone, Debug)]
pub struct MappingConfiguration1x1 {
    pub node_frequency: Frequency,
    pub link_frequency: Frequency,
    pub link_latency: Latency,
    /// Size of frame in bits.
    pub frame_size: usize,
    pub io_memory_size: usize,
    /// Number of cycles required to evaluate a service node.
    ///
    /// TODO(pouyad) Service nodes need to be lowered with some notion of
    /// performance. Assume they uniformly take the same number of local cycles
    /// on their target ComputeNode for now.
    pub compute_cycles_per_service_node: usize,
}

impl Default for MappingConfiguration1x1 {
    fn default() -> Self {
        Self {
            node_frequency: Frequency::new(1),
            link_frequency: Frequency::new(1),
            link_latency: Latency(0),
            frame_size: crate::hw::config::FRAME_SIZE,
            io_memory_size: LinkConfiguration::default().memory_size,
            compute_cycles_per_service_node: 1,
        }
    }
}

/// Similar configuration to `MappingConfiguration1x1` for the OneToOneNetwork HW
/// mapping.
#[derive(Clone, Debug)]
pub struct MappingConfiguration1x1Network {
    pub node_frequency: Frequency,
    pub link_frequency: Frequency,
    pub link_latency: Latency,
    /// Size of frame in bits.
    pub frame_size: usize,
    pub io_memory_size: usize,
    pub crossbar_latency: Latency,
    /// Number of cycles required to evaluate a service node.
    ///
    /// TODO(pouyad) Service nodes need to be lowered with some notion of
    /// performance. Assume they uniformly take the same number of local cycles
    /// on their target ComputeNode for now.
    pub compute_cycles_per_service_node: usize,
}

impl Default for MappingConfiguration1x1Network {
    fn default() -> Self {
        Self {
            node_frequency: Frequency::new(1),
            link_frequency: Frequency::new(1),
            link_latency: Latency(0),
            frame_size: crate::hw::config::FRAME_SIZE,
            compute_cycles_per_service_node: 1,
            crossbar_latency: Latency(1),
            io_memory_size: LinkConfiguration::default().memory_size,
        }
    }
}

/// Each system-node is a knapsack of application nodes, find the embedded
/// application nodes for each system node.
fn get_compute_node_service_functions(
    app_spec: &Application,
    alloc: &SystemAllocation,
) -> HashMap<NodeIndex, Vec<NodeIndex>> {
    let mut system_node_knapsack: HashMap<NodeIndex, Vec<NodeIndex>> = HashMap::new();
    for app_node_id in app_spec.iter_nodes() {
        let sys_node = &alloc.nodes[&ServiceHandle::new(app_spec.id(), app_node_id)];
        if let Some(knapsack) = system_node_knapsack.get_mut(&sys_node) {
            knapsack.push(app_node_id);
        } else {
            system_node_knapsack.insert(*sys_node, vec![app_node_id]);
        }
    }
    system_node_knapsack
}

/// For each compute node in the HW system tally the number of frames for the
/// inputs and outputs.
fn tally_io_frame_counts(
    app_spec: &Application,
    system_spec: &HardwareSpec,
    system_node_knapsack: &HashMap<NodeIndex, Vec<NodeIndex>>,
) -> (
    HashMap<NodeIndex, Vec<usize>>,
    HashMap<NodeIndex, Vec<usize>>,
) {
    let mut input_frame_counts: HashMap<NodeIndex, Vec<usize>> = HashMap::new();
    let mut output_frame_counts: HashMap<NodeIndex, Vec<usize>> = HashMap::new();
    for sys_node_id in system_spec.compute_nodes().iter() {
        input_frame_counts.insert(
            *sys_node_id,
            vec![0; system_spec.get_input_links(*sys_node_id).count()],
        );
        output_frame_counts.insert(
            *sys_node_id,
            vec![0; system_spec.get_output_links(*sys_node_id).count()],
        );
        for app_node_id in system_node_knapsack[&sys_node_id].iter() {
            let app_node = app_spec.get_node(*app_node_id);
            for (input_port, edge_ref) in system_spec.get_input_links(*sys_node_id).enumerate() {
                let link = system_spec.get_link(edge_ref.id());
                let frame_size = link.frame_size();
                let msg_size = app_node.borrow().get_msg_size(Port::new_in(input_port));
                let frame_count = msg_size / frame_size + usize::from(msg_size % frame_size != 0);
                let frame_counts = input_frame_counts.get_mut(&sys_node_id).unwrap();
                frame_counts[input_port] += frame_count;
            }
            for (output_port, edge_ref) in system_spec.get_output_links(*sys_node_id).enumerate() {
                let link = system_spec.get_link(edge_ref.id());
                let frame_size = link.frame_size();
                let msg_size = app_node.borrow().get_msg_size(Port::new_out(output_port));
                let frame_count = msg_size / frame_size + usize::from(msg_size % frame_size != 0);
                let frame_counts = output_frame_counts.get_mut(&sys_node_id).unwrap();
                frame_counts[output_port] += frame_count;
            }
        }
    }
    (input_frame_counts, output_frame_counts)
}

// Compute the required number of input batching rounds for the given frame count and
// batch-size. That is, given K frames and a batch size B, return ceil(K/B).
fn compute_input_batch_rounds_1x1(
    system_spec: &HardwareSpec,
    input_frame_counts: &HashMap<NodeIndex, Vec<usize>>,
    edge_to_path_map: &HashMap<EdgeIndex, &Path>,
) -> HashMap<NodeIndex, Vec<usize>> {
    input_frame_counts
        .iter()
        .map(|(sys_node_id, frame_counts)| {
            let batch_rounds_per_input = frame_counts
                .iter()
                .zip(system_spec.get_input_links(*sys_node_id))
                .map(|(frame_count, edge_ref)| {
                    let path = edge_to_path_map[&edge_ref.id()];
                    let batching = compute_batch_size(system_spec, path);
                    let path_latency = path.path_latencies(system_spec);
                    let latency = path_latency[&edge_ref.id()];
                    let (tx_node, _) = system_spec.get_link_endpoints(path.source());
                    let tx_clock = system_spec
                        .get_node(tx_node)
                        .borrow()
                        .into_provisioned_node()
                        .unwrap()
                        .starting_cycles() as i64;
                    let rx_clock = tx_clock + latency;
                    log::trace!(
                        "compute_input_batch_rounds_1x1 path {:?} tx clock = {:?} rx clock {:?}",
                        path,
                        tx_clock,
                        rx_clock
                    );
                    let (_, rx_node) = system_spec.get_link_endpoints(edge_ref.id());
                    let rx_starting_cycles = system_spec
                        .get_node(rx_node)
                        .borrow()
                        .into_provisioned_node()
                        .unwrap()
                        .starting_cycles() as i64;
                    let delay_since_start_of_metacycle = rx_clock - rx_starting_cycles;
                    assert!(delay_since_start_of_metacycle >= 0);
                    let frame_ticks = frame_count + delay_since_start_of_metacycle as usize;
                    let batch_rounds = frame_ticks / batching.batch_size
                        + usize::from(frame_ticks % batching.batch_size != 0);
                    batch_rounds
                })
                .collect::<Vec<_>>();
            (*sys_node_id, batch_rounds_per_input)
        })
        .collect::<HashMap<_, _>>()
}

// Compute the required number of output batching rounds for the given frame count and
// batch-size. That is, given K frames and a batch size B, return ceil(K/B).
fn compute_output_batch_rounds_1x1(
    system_spec: &HardwareSpec,
    output_frame_counts: &HashMap<NodeIndex, Vec<usize>>,
    edge_to_path_map: &HashMap<EdgeIndex, &Path>,
) -> HashMap<NodeIndex, Vec<usize>> {
    output_frame_counts
        .iter()
        .map(|(sys_node_id, frame_counts)| {
            let batch_rounds_per_output = frame_counts
                .iter()
                .zip(system_spec.get_output_links(*sys_node_id))
                .map(|(frame_count, edge_ref)| {
                    let path = edge_to_path_map[&edge_ref.id()];
                    let batching = compute_batch_size(system_spec, path);
                    let batch_rounds = frame_count / batching.batch_size
                        + usize::from(frame_count % batching.batch_size != 0);
                    batch_rounds
                })
                .collect::<Vec<_>>();
            (*sys_node_id, batch_rounds_per_output)
        })
        .collect::<HashMap<_, _>>()
}

fn compute_network_cpm_1x1(
    system_spec: &HardwareSpec,
    input_batch_rounds: &HashMap<NodeIndex, Vec<usize>>,
    output_batch_rounds: &HashMap<NodeIndex, Vec<usize>>,
    edge_to_path_map: &HashMap<EdgeIndex, &Path>,
) -> HashMap<NodeIndex, usize> {
    system_spec
        .compute_nodes()
        .iter()
        .map(|sys_node_id| {
            let sys_node = system_spec.get_node(*sys_node_id);
            let sys_node_freq = sys_node.borrow().frequency().value;
            let node_ticks_per_batch = system_spec
                .get_input_links(*sys_node_id)
                .chain(system_spec.get_output_links(*sys_node_id))
                .map(|edge_ref| {
                    let link = system_spec.get_link(edge_ref.id());
                    let link_freq = link.into_provisioned_link().unwrap().frequency().value;
                    let batching =
                        compute_batch_size(system_spec, &edge_to_path_map[&edge_ref.id()]);
                    let batch_times_node_freq = batching.batch_size * sys_node_freq;
                    assert!(batch_times_node_freq % link_freq == 0);
                    let node_ticks_per_batch = batch_times_node_freq / link_freq;
                    node_ticks_per_batch
                })
                .collect::<Vec<_>>();
            let (node_ticks_per_input_batch, node_ticks_per_output_batch) =
                node_ticks_per_batch.split_at(system_spec.get_input_links(*sys_node_id).count());
            let num_cycles_per_input = node_ticks_per_input_batch
                .iter()
                .zip(&input_batch_rounds[&sys_node_id])
                .map(|(ticks_per_batch, batch_rounds)| ticks_per_batch * batch_rounds);
            let num_cycles_per_output = node_ticks_per_output_batch
                .iter()
                .zip(&output_batch_rounds[&sys_node_id])
                .map(|(ticks_per_batch, batch_rounds)| ticks_per_batch * batch_rounds);
            (
                *sys_node_id,
                num_cycles_per_input
                    .chain(num_cycles_per_output)
                    .max()
                    .unwrap(),
            )
        })
        .collect::<HashMap<_, _>>()
}

/// Return the integer multiple of each compute node's frequency as a multiple
/// of the GCD of all compute node frequencies.
fn node_frequency_ratios(system_spec: &HardwareSpec) -> HashMap<NodeIndex, usize> {
    let node_frequencies = system_spec
        .iter_nodes()
        .map(|node_id| {
            system_spec
                .get_node(node_id)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .frequency()
                .value
        })
        .collect::<Vec<_>>();
    let gcd_node_frequencies = node_frequencies[1..]
        .iter()
        .fold(node_frequencies[0], |accum, value| {
            num::integer::gcd(accum, *value)
        });
    let node_frequency_ratios = system_spec
        .iter_nodes()
        .zip(node_frequencies.iter())
        .map(|(node_id, f)| {
            assert!(f % gcd_node_frequencies == 0);
            (node_id, f / gcd_node_frequencies)
        })
        .collect::<HashMap<_, _>>();
    node_frequency_ratios
}

/// Since nodes operate at different frequencies in general we need to find
/// an system-wide duration for the metacycle that can be translated back to
/// an integer number of *local* cycles per node. Calculated as a integer multiple
/// of the LcmPeriod.
fn compute_system_wide_period_1x1(
    system_spec: &HardwareSpec,
    alloc: &SystemAllocation,
    comms_cycles_per_metacycle: &HashMap<NodeIndex, usize>,
) -> usize {
    // The minimum number of *local* cycles per metacycle for each node in the system.
    let cycles_per_metacycle: HashMap<NodeIndex, usize> = alloc
        .nodes
        .iter()
        .map(|(app_node, sys_node_id)| {
            (
                *sys_node_id,
                max(
                    alloc.compute_cycles[&app_node],
                    comms_cycles_per_metacycle[&sys_node_id],
                ),
            )
        })
        .collect::<HashMap<_, _>>();

    let all_freq_ratios = node_frequency_ratios(system_spec);
    let freq_ratios = all_freq_ratios
        .iter()
        .filter(|(node_id, _)| {
            system_spec
                .get_node(**node_id)
                .borrow()
                .into_provisioned_switch_node()
                .is_none()
        })
        .collect::<HashMap<_, _>>();
    let (max_node_id, ratio_numerator) = cycles_per_metacycle
        .iter()
        .max_by(|cpm1, cpm2| {
            let (node1_id, x) = cpm1;
            let (node2_id, u) = cpm2;
            let y = freq_ratios[node1_id];
            let v = freq_ratios[node2_id];
            // a = x/y, b = u/v
            //
            // To avoid floating-point operations we compare the fractions via
            // x/y > u/v => x*v > u*y
            let x_v: u128 = (**x as u128) * (*v as u128);
            let u_y: u128 = (**u as u128) * (*y as u128);
            if x_v > u_y {
                std::cmp::Ordering::Greater
            } else if x_v < u_y {
                std::cmp::Ordering::Less
            } else {
                std::cmp::Ordering::Equal
            }
        })
        .unwrap();
    let ratio_denominator = freq_ratios[max_node_id];
    // The system wide period is an integer multiple of LcmPeriod.
    *ratio_numerator / *ratio_denominator + usize::from(ratio_numerator % ratio_denominator != 0)
}

/// Set computed CPMs for each compute node and the IO memory sizes.
fn set_cpms(system_spec: &HardwareSpec, system_wide_period: usize) {
    let freq_ratios = node_frequency_ratios(system_spec);
    for node_id in system_spec.compute_nodes().iter() {
        let node = system_spec.get_node(*node_id);
        let node_cycles_per_metacycle = system_wide_period * freq_ratios[node_id];
        node.borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_cycles_per_metacycle([node_cycles_per_metacycle; BUFFERING_DOUBLE]);
        log::trace!(
            "time_physical_system_1x1 setting CPM for node {} to {}",
            node.borrow().name(),
            node_cycles_per_metacycle
        );
    }
}

fn get_switch_calendars_1x1_network(
    app_spec: &Application,
    system_spec: &HardwareSpec,
    alloc: &SystemAllocation,
    system_wide_period: usize,
) -> HashMap<NodeIndex, CrossbarCalendar> {
    let freq_ratios = node_frequency_ratios(system_spec);
    let mut switch_calendars = HashMap::new();
    for (app_edge, path) in alloc.links.iter() {
        let path = path.as_ref().unwrap();
        assert_eq!(path.all_links().len(), 3);
        let (_, src_switch_id) = system_spec.get_link_endpoints(path.source());
        let (dst_switch_id, _) = system_spec.get_link_endpoints(path.destinations()[0]);
        assert!(system_spec
            .get_node(src_switch_id)
            .borrow()
            .into_provisioned_switch_node()
            .is_some());
        assert!(system_spec
            .get_node(dst_switch_id)
            .borrow()
            .into_provisioned_switch_node()
            .is_some());
        let (src_app_node_id, dst_app_node_id) = app_spec.get_link_endpoints(app_edge.edge_id);
        if !switch_calendars.contains_key(&src_switch_id) {
            switch_calendars.insert(
                src_switch_id,
                generate_switch_crossbar_calendar_1x1_network(
                    app_spec,
                    system_spec,
                    system_wide_period,
                    &freq_ratios,
                    src_app_node_id,
                    src_switch_id,
                ),
            );
        }
        if !switch_calendars.contains_key(&dst_switch_id) {
            switch_calendars.insert(
                dst_switch_id,
                generate_switch_crossbar_calendar_1x1_network(
                    app_spec,
                    system_spec,
                    system_wide_period,
                    &freq_ratios,
                    dst_app_node_id,
                    dst_switch_id,
                ),
            );
        }
    }
    switch_calendars
}

fn generate_switch_crossbar_calendar_1x1_network(
    app_spec: &Application,
    system_spec: &HardwareSpec,
    system_wide_period: usize,
    freq_ratios: &HashMap<NodeIndex, usize>,
    app_node_id: NodeIndex,
    switch_id: NodeIndex,
) -> CrossbarCalendar {
    // Set the switch CPM.
    let switch_node_freq = system_spec
        .get_node(switch_id)
        .borrow()
        .into_provisioned_node()
        .unwrap()
        .frequency()
        .value;
    assert!(system_spec
        .get_input_links(switch_id)
        .chain(system_spec.get_output_links(switch_id))
        .all(|edge_ref| {
            switch_node_freq
                == system_spec
                    .get_link(edge_ref.id())
                    .into_provisioned_link()
                    .unwrap()
                    .frequency()
                    .value
        }));
    let switch_cpm = system_wide_period * freq_ratios[&switch_id];
    {
        system_spec
            .get_node(switch_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_cycles_per_metacycle([switch_cpm; BUFFERING_DOUBLE]);
    }
    let app_input_port_count = app_spec.get_input_links(app_node_id).count() as u32;
    let app_output_port_count = app_spec.get_output_links(app_node_id).count() as u32;
    {
        let identity_routing = (app_output_port_count
            ..app_input_port_count + app_output_port_count)
            .chain(0..app_output_port_count)
            .collect::<Vec<_>>();
        let crossbar_calendar = vec![CrossbarCalendarEntry::new(
            Some(identity_routing),
            switch_cpm,
        )];
        log::trace!(
            "time_physical_system_1x1 Setting switch {:?} cpm {} crossbar calendar {:?}",
            switch_id,
            switch_cpm,
            crossbar_calendar
        );
        crossbar_calendar
    }
}

/// Given an app, the 1x1 physical system and corresponding allocation. Size the
/// physical system appropriately.
///
///  When all components under simulation operate at the same (unit) frequency,
///  for the tuple (Gather, Link, Scatter) a frame is processed by each element
///  of the tuple per cycle. When individual elements in the tuple operate at
///  different frequencies then we can solve for a batch (B) such that for
///  every M ticks of Gather, and N ticks of Scatter, B frames are
///  communicated.
///
///  If there were a total of K frames to be communicated, then `Q = ceil( K / B )`
///  rounds of batches would be required to communicate all the data. This
///  requires `Q*M` cycles by the gather, and `Q*N` cycles by the corresponding
///  scatter.
///
///  In reality we have `Q_i * B_i` cycles required for scatters i on a node, and
///  `Q_j * B_j` required for gathers j on a node. The number of cycles required
///  for comms is therefore,
///
///```text
///  K_i = ApplicationMsgSize(Scatter(i)) + LinkLatency(i, j)   // Measured in # of HW frames
///  K_j = ApplicationMsgSize(Gather(j))
///  Q_i = ceil( K_i / B_i )
///  Q_j = ceil( K_j / B_j )
///```
///  NOTE: Quite importantly `Q_i/Q_j` assume conflict-free routing of frames during
///  comms.
///
///```text
///  RequiredCommunicationCycles(node_k) = max({Q_i * N_i}, {Q_j * M_i})
///  MemorySize(Scatter(i)) = K_i
///  MemorySize(Gather(j)) = K_j
///
///  CyclesPerMetacycle(node_k) = max(RequiredComputeCycles(node_k),
///  RequiredCommunicationCycles(node_k))
///```
///  `CyclesPerMetacycle(node_k)` gives each node enough cycles to perform its
///  compute for the given metacycle and enough cycles to send/receive the
///  required number of batches to meet it's IO requirements.
///
///  Each node needs to spend a minimum of `CyclesPerMetacycle(node_k)`. But in
///  order for the system to work, comms/compute have to align between all the
///  nodes,  and consequently they need to find a system-wide cycles per
///  metacycle with equal duration for all the nodes operating at different
///  frequencies.
///
///  E.g., The duration of node `A`'s metacycle would be
///
///  `MetacycleDuration(A) = CyclesPerMetacycle(node_A) / frequency(A)`
//
///  while node `B` would have
///
///  `MetacycleDuration(B) = CyclesPerMetacycle(node_B) / frequency(B)`
///
///  We want `MetacycleDuration(node_k)` to be the same for all `node_k`, and
///  since we can't alter `frequency(node_k)` we must adjust
///  `CyclesPerMetacycle(node_k)` to that end.
///
///  let `LcmPeriod = LCM({ 1 / frequency(node_k) }) = 1 / GCD({ frequency(node_k) })`
//
///  let `MaxDuration = max({ MetacycleDuration(node_k) })` then
///
///```text
///       SystemWidePeriod = ceil(MaxDuration / LcmPeriod)
///                        = ceil(max({ CyclesPerMetacycle(node_k) /  }) * GCD({ frequency(node_k) }))
///                        = ceil(max({ CyclesPerMetacycle(node_k) / (frequency(node_k) / GCD({ frequency(node_k) }))}))
///```
///
///  if we let `FrequencyRatio(node_k) = frequency(node_k) / GCD({ frequency(node_k) })`
//
///  then `SystemWidePeriod = ceil(max({ CyclesPerMetacycle(node_k) / FrequencyRatio(node_k) }))`
///
///  and for each node,
///```text
///  SystemWideCyclesPerMetacycle(node_k) = SystemWidePeriod * LcmPeriod / (1 / frequency(node_k))
///                                       = SystemWidePeriod * (1 / GCD({ frequency(node_k) })) / (1 / frequency(node_k))
///                                       = SystemWidePeriod * frequency(node_k) / GCD({ frequency(node_k) }) // an integer
///                                       = SystemWidePeriod * FrequencyRatio(node_k)
///```
fn time_physical_system_1x1(
    app_spec: &Application,
    system_spec: &HardwareSpec,
    alloc: &SystemAllocation,
) -> usize {
    // TODO(pouyad) Assert that all application nodes have unit rates of service
    // for the time being. Multiple rates of service could mean that the
    // application's service node may not have a 1:1 mapping to system compute
    // nodes.
    assert!(app_spec
        .iter_nodes()
        .map(|app_node_id| {
            app_spec
                .get_node(app_node_id)
                .borrow()
                .into_application_node()
                .unwrap()
                .rate_of_service()
        })
        .all(|rate_of_service| rate_of_service.0 == 1));

    // Find the knapsack of service functions assigned to compute nodes.
    let system_node_knapsack = get_compute_node_service_functions(app_spec, alloc);
    // In the 1x1 mapping there should only ever be a single application mapped
    // to a compute node.
    assert!(system_node_knapsack
        .iter()
        .all(|(_sys_node_id, app_node_ids)| { app_node_ids.len() == 1 }));

    // Mapping of system edges to paths - because this is a 1x1 assignment this
    // is guaranteed to be unique.
    let edge_to_path_map = alloc
        .links
        .values()
        .flat_map(|path| {
            let path = path.as_ref().unwrap();
            path.all_links()
                .iter()
                .map(|link_id| (*link_id, path))
                .collect::<Vec<_>>()
        })
        .collect::<HashMap<_, _>>();

    // Find K_i and K_j for each system node.
    //
    // TODO(pouyad) In an SDF graph this depends on the number of input tokens
    // that a service will consume on each input per firing. aegir doesn't
    // encode this information for the time being and assumes this number to be
    // 1.
    let (input_frame_counts, output_frame_counts) =
        tally_io_frame_counts(app_spec, system_spec, &system_node_knapsack);
    log::trace!(
        "time_physical_system_1x1 input_frame_counts {:#?}",
        input_frame_counts
    );
    log::trace!(
        "time_physical_system_1x1 output_frame_counts {:#?}",
        output_frame_counts
    );

    // Compute Q_i and Q_j for each system node.
    let input_batch_rounds =
        compute_input_batch_rounds_1x1(system_spec, &input_frame_counts, &edge_to_path_map);
    let output_batch_rounds =
        compute_output_batch_rounds_1x1(system_spec, &output_frame_counts, &edge_to_path_map);
    log::trace!(
        "time_physical_system_1x1 input_batch_rounds {:#?}",
        input_batch_rounds
    );
    log::trace!(
        "time_physical_system_1x1 output_batch_rounds {:#?}",
        output_batch_rounds
    );

    // Compute minimum required cycles per metacycle for each node's comms.
    let comms_cycles_per_metacycle: HashMap<NodeIndex, usize> = compute_network_cpm_1x1(
        system_spec,
        &input_batch_rounds,
        &output_batch_rounds,
        &edge_to_path_map,
    );
    log::trace!(
        "time_physical_system_1x1 comms cpm {:#?}",
        comms_cycles_per_metacycle
    );
    let system_wide_period =
        compute_system_wide_period_1x1(system_spec, alloc, &comms_cycles_per_metacycle);
    set_cpms(system_spec, system_wide_period);
    system_wide_period
}

/// Creates a physical topology, equivalent to the application specification.
/// This physical topology is still not configured to contain the correct memory
/// sizes on link endpoints and the configured to a known metacycle size.
pub(super) fn generate_physical_system_1x1(
    app_spec: &Application,
    mapping_cfg: &MappingConfiguration1x1,
) -> HardwareSpec {
    let mut system_spec = HardwareSpec::new();

    // create all the nodes first, so that we have link destinations available
    let mut nodes_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();
    let global_link_config = LinkConfiguration {
        frequency: mapping_cfg.link_frequency.value,
        latency: mapping_cfg.link_latency.0,
        frame_size: mapping_cfg.frame_size,
        memory_size: mapping_cfg.io_memory_size,
        ..Default::default()
    };

    for app_node_id in app_spec.iter_nodes() {
        let app_node = app_spec.get_node(app_node_id);
        let mut node_config = NodeConfiguration {
            frequency: mapping_cfg.node_frequency.value,
            ..Default::default()
        };
        for edge in app_spec.get_input_links(app_node_id) {
            node_config.add_link(
                &global_link_config,
                Port::new(
                    edge.weight().dst_port().into(),
                    &PortProperties {
                        direction: Direction::Incoming,
                        frame_size: FrameSize::Number(mapping_cfg.frame_size),
                        ..Default::default()
                    },
                ),
            );
        }
        for edge in app_spec.get_output_links(app_node_id) {
            node_config.add_link(
                &global_link_config,
                Port::new(
                    edge.weight().src_port().into(),
                    &PortProperties {
                        direction: Direction::Outgoing,
                        frame_size: FrameSize::Number(mapping_cfg.frame_size),
                        ..Default::default()
                    },
                ),
            );
        }
        let app_name = &app_node.as_ref().borrow().name().to_string();
        log::trace!(
            "generate_physical_system_1x1 node configuration name: {} id: {} config: {:#?}",
            app_name,
            app_node_id.index(),
            node_config
        );
        let sys_node_id = system_spec.add_node(Node::ComputeNode(ComputeNode::from_config(
            app_name.as_str(),
            &node_config,
        )));
        // set the application
        system_spec.get_node(sys_node_id).borrow_mut().register_app(
            ServiceHandle::new(app_spec.id(), app_node_id),
            Rc::clone(&app_node),
        );
        nodes_map.insert(app_node_id, sys_node_id);
    }

    // iterate through all the nodes and create the links
    for app_node_id in app_spec.iter_nodes() {
        let sys_src_id = nodes_map.get(&app_node_id).unwrap();
        for edge in app_spec.get_output_links(app_node_id) {
            let app_dst_id = edge.target();
            let sys_dst_id = nodes_map.get(&app_dst_id).unwrap();
            let link_spec = edge.weight();
            let link = hw::Link::from_config(
                link_spec.src_port().into(),
                link_spec.dst_port().into(),
                LinkConfiguration {
                    frame_size: mapping_cfg.frame_size,
                    ..global_link_config
                },
            );
            system_spec.link_simplex(*sys_src_id, *sys_dst_id, link);
        }
    }

    system_spec
}

/// Creates a physical topology as described by AllocationPolicy::OneToOneNetwork
pub(super) fn generate_physical_system_1x1_network(
    app_spec: &Application,
    mapping_cfg: &MappingConfiguration1x1Network,
) -> HardwareSpec {
    let mut system_spec = HardwareSpec::new();

    #[derive(Clone, Debug)]
    struct SwitchNodeDeferred {
        name: String,
        cfg: SwitchConfiguration,
    }

    #[derive(Clone, Debug)]
    struct NodePairDeferred {
        compute_node: NodeIndex,
        switch_node: SwitchNodeDeferred,
    }

    #[derive(Clone, Debug)]
    struct NodePair {
        compute_node: NodeIndex,
        switch_node: NodeIndex,
    }

    // Create all the *compute* nodes first: since this is a 1:1 mapping, we need the
    // iteration order of app_nodes and compute nodes to line up. Switch nodes are
    // deferred to be created after all the compute nodes. The order matters here, so
    // we use a vector of tuples vs. a hashmap.
    let mut nodes_map_deferred: Vec<(NodeIndex, NodePairDeferred)> = vec![];
    let global_link_config = LinkConfiguration {
        frequency: mapping_cfg.link_frequency.value,
        latency: mapping_cfg.link_latency.0,
        frame_size: mapping_cfg.frame_size,
        memory_size: mapping_cfg.io_memory_size,
        ..Default::default()
    };

    for app_node_id in app_spec.iter_nodes() {
        let app_node = app_spec.get_node(app_node_id);
        let mut node_config = NodeConfiguration {
            frequency: mapping_cfg.node_frequency.value,
            ..Default::default()
        };
        for edge in app_spec.get_input_links(app_node_id) {
            node_config.add_link(
                &global_link_config,
                Port::new(
                    edge.weight().dst_port().into(),
                    &PortProperties {
                        direction: Direction::Incoming,
                        frame_size: FrameSize::Number(mapping_cfg.frame_size),
                        ..Default::default()
                    },
                ),
            );
        }
        for edge in app_spec.get_output_links(app_node_id) {
            node_config.add_link(
                &global_link_config,
                Port::new(
                    edge.weight().src_port().into(),
                    &PortProperties {
                        direction: Direction::Outgoing,
                        frame_size: FrameSize::Number(mapping_cfg.frame_size),
                        ..Default::default()
                    },
                ),
            );
        }
        // A compute node has n outputs and m inputs
        //
        //   +-----+
        //   |  c  |-----> n
        //   |     |<----- m
        //   +-----+
        //
        // The switch has n + m inputs and n + m outputs,
        //    * inputs 0..n of the switch are connected to the compute node, and
        //      inputs n..n+m are connected to other switches.
        //    * outputs 0..m of the switch are connected to the compute node, and
        //      outputs m..n+m are connected to other switches.
        //
        //   +-----+       +-----+
        //   |  c  |---n-->|  X  |---->n
        //   |     |<--m---|     |<----m
        //   +-----+       +-----+
        //
        // Output i  of compute node c is mapped to input i of the switch X, which
        // is routed to output m + i of the switch.
        //
        // Input j of compute node c is mapped to output j of the switch X, which
        // is routed from input n + j of the switch.
        //
        // The switch crossbar will therefore be programmed via,
        //
        // [n, n + 1, n + 2, ..., n + m - 1, 0, 1, 2, 3, ..., n - 1]
        //
        // i.e., routing input(n)     -> output(0)
        //               input(n + 1) -> output(1)
        // etc.

        let switch_config = SwitchConfiguration {
            input_link_count: node_config.num_inputs() + node_config.num_outputs(),
            output_link_count: node_config.num_outputs() + node_config.num_inputs(),
            crossbar_latency: mapping_cfg.crossbar_latency.0,
            link_configuration: LinkConfiguration {
                frame_size: mapping_cfg.frame_size,
                memory_size: 1,
                ..Default::default()
            },
            ..Default::default()
        };
        let app_name = &app_node.borrow().name().to_string();
        let switch_name = format!("{}_switch", app_name);
        log::trace!(
            "generate_physical_system_1x1_network node configuration name: {} id: {} config: {:#?}",
            app_name,
            app_node_id.index(),
            node_config
        );
        log::trace!(
            "generate_physical_system_1x1_network switch configuration name: {} id: {} config: {:#?}",
            app_name,
            app_node_id.index(),
            switch_config
        );
        let sys_node_id = system_spec.add_node(Node::ComputeNode(ComputeNode::from_config(
            app_name.as_str(),
            &node_config,
        )));
        // set the application
        system_spec.get_node(sys_node_id).borrow_mut().register_app(
            ServiceHandle::new(app_spec.id(), app_node_id),
            Rc::clone(&app_node),
        );
        nodes_map_deferred.push((
            app_node_id,
            NodePairDeferred {
                compute_node: sys_node_id,
                switch_node: SwitchNodeDeferred {
                    name: switch_name,
                    cfg: switch_config,
                },
            },
        ));
    }

    // Now create all the switch nodes. These appear after all the compute nodes in the HW graph's
    // node iteration order.
    let nodes_map = nodes_map_deferred
        .iter()
        .map(|(app_node_id, defer)| {
            let switch_node_id = system_spec.add_node(Node::SwitchNode(SwitchNode::from_config(
                defer.switch_node.name.as_str(),
                &defer.switch_node.cfg,
            )));
            (
                app_node_id,
                NodePair {
                    compute_node: defer.compute_node,
                    switch_node: switch_node_id,
                },
            )
        })
        .collect::<HashMap<_, _>>();

    // Iterate through all the nodes and create the links.
    for app_node_id in app_spec.iter_nodes() {
        let node_pair = nodes_map.get(&app_node_id).unwrap();
        // For each app node s(i)
        //  +------+          +------+
        //  | s(i) |--------->| s(j) |
        //  |      |          |      |
        //  +------+          +------+
        //
        // for each output connection c(s(i), s(j))
        //   - create link l(X(i), X(j))
        //   - create link l(c(i), X(i))
        //
        //  +------+  l(X(i),X(j))  +------+
        //  | X(i) |--------------->| X(j) |
        //  |      |                |      |
        //  +------+                +------+
        //    ^
        //    | l(c(i),X(i))
        //  +------+
        //  | c(i) |
        //  |      |
        //  +------+
        let src_app_input_port_count = app_spec.get_input_links(app_node_id).count();
        for edge in app_spec.get_output_links(app_node_id) {
            let app_dst_id = edge.target();
            let dst_node_pair = nodes_map.get(&app_dst_id).unwrap();
            let connection = edge.weight();
            let src_port: usize = connection.src_port().into();

            // Link from compute node to the switch: l(c(i), X(i))
            let node_to_switch_link = hw::Link::from_config(src_port, src_port, global_link_config);
            system_spec.link_simplex(
                node_pair.compute_node,
                node_pair.switch_node,
                node_to_switch_link,
            );
            // Link from the switch to the corresponding switch l(X(i), X(j))
            let (_, dst_app_node_id) = app_spec.get_link_endpoints(edge.id());
            let dst_app_output_port_count = app_spec.get_output_links(dst_app_node_id).count();
            let dst_port: usize = connection.dst_port().into();
            let switch_to_switch_link = hw::Link::from_config(
                // src-app inputs are src-switch outputs
                src_app_input_port_count + src_port,
                // dst-app outputs are dst-switch inputs
                dst_app_output_port_count + dst_port,
                global_link_config,
            );
            system_spec.link_simplex(
                node_pair.switch_node,
                dst_node_pair.switch_node,
                switch_to_switch_link,
            );
        }
        // For each incoming edge c(s(j), s(i)) to service s(i)
        //
        //  +------+          +------+
        //  | s(i) |          | s(j) |
        //  |      |<---------|      |
        //  +------+          +------+
        //
        // Create l(X(i), c(i))
        //
        //  +------+
        //  | X(i) |
        //  |      |
        //  +------+
        //       |
        //       v l(X(i),c(i))
        //  +------+
        //  | c(i) |
        //  |      |
        //  +------+
        for edge in app_spec.get_input_links(app_node_id) {
            let connection = edge.weight();
            let dst_port = connection.dst_port().into();
            let switch_to_node_link = hw::Link::from_config(dst_port, dst_port, global_link_config);
            system_spec.link_simplex(
                node_pair.switch_node,
                node_pair.compute_node,
                switch_to_node_link,
            );
        }
    }

    system_spec
}
