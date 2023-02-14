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

use crate::specs::*;
use crate::vcd::{ChangeValue, VcdWriter, DEFAULT_TOP_MODULE};
use crate::Port;

use bitvec::prelude::*;
use log::trace;
use petgraph::prelude::*;
mod bittide_sim;
use crate::calendar::Buffering;
use crate::calendar::APPLICATION_NODE;
pub use bittide_sim::generate_system_spec;
pub use bittide_sim::simulate_bittide;
pub use bittide_sim::simulate_bittide_app;
pub use bittide_sim::Inspect;
use rand::{Rng, RngCore, SeedableRng};
use rand_xoshiro::Xoshiro256StarStar;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum SimulationType {
    Software,
    Hardware,
}

/// Common intrface for HW and SW simulators
pub trait SystemSimulationTrait<const BUFFERING: Buffering> {
    /// Step all nodes in the system by one cycle
    fn simulate_system_one_cycle<
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + Clone + std::fmt::Debug,
    >(
        &mut self,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
        callbacks: OptionSimCallbacks,
    );

    /// Query the simulation type
    fn sim_type(&self) -> SimulationType;
}

struct LinkBuffer {
    /// Circular buffer holding link-data for the simulator.
    buffer: Vec<DataWithValidity>,

    /// The write pointer into the circular buffer (source of frames).
    write_idx: usize,

    /// The read pointer into the circular buffer (sink of frames).
    read_idx: usize,

    /// The number of frames in the frames buffer.
    occupancy: usize,
}

impl LinkBuffer {
    fn new(buffer_size: usize, frame_size: usize, latency: Latency) -> Self {
        let latency_value = latency.0;
        Self {
            buffer: vec![
                DataWithValidity {
                    data: BitVec::repeat(false, frame_size).into_boxed_bitslice(),
                    valid: false,
                };
                buffer_size + latency_value
            ],
            write_idx: latency_value,
            read_idx: 0,
            occupancy: latency_value,
        }
    }

    /// Get write slots, which the caller can use to write frames to the link buffer. (Fills the link.)
    fn write_frames(&mut self, frame_count: usize) -> Vec<&mut DataWithValidity> {
        trace!(
            "(pre) write_frames write_idx: {}, occupancy: {}",
            self.write_idx,
            self.occupancy,
        );
        assert!(
            frame_count <= self.buffer.len() - self.occupancy,
            "May not request more frames than available."
        );
        self.occupancy += frame_count;
        // Get frame references [start_idx, end_idx) where end_idx could possibly wrap around the buffer.
        let start_idx = self.write_idx;
        let end_idx = (self.write_idx + frame_count) % self.buffer.len();
        let (left, right) = self.buffer.split_at_mut(start_idx);
        trace!(
            "(post) write_frames  write_idx: {}, occupancy: {}",
            end_idx,
            self.occupancy,
        );
        self.write_idx = end_idx;
        if right.len() >= frame_count {
            // No wrap around.
            let (frames, _) = right.split_at_mut(frame_count);
            frames.iter_mut().collect()
        } else {
            // Wrap around.
            let wrapped_frame_count = frame_count - right.len();
            let (wrapped_frames, _) = left.split_at_mut(wrapped_frame_count);
            right.iter_mut().chain(wrapped_frames.iter_mut()).collect()
        }
    }

    /// Read from the link. (Drains the link.)
    fn read_frames(&mut self, frame_count: usize) -> Vec<&DataWithValidity> {
        trace!(
            "(pre) read_frames read_idx: {}, occupancy: {}",
            self.read_idx,
            self.occupancy,
        );
        assert!(
            frame_count <= self.occupancy,
            "May not request more frames than available."
        );
        // Get frame references [start_idx, end_idx) where end_idx could possibly wrap around the buffer.
        let start_idx = self.read_idx;
        let end_idx = (self.read_idx + frame_count) % self.buffer.len();
        self.occupancy -= frame_count;
        trace!(
            "(post) read_frames read_idx: {}, occupancy: {}",
            end_idx,
            self.occupancy,
        );
        let (left, right) = self.buffer.split_at(start_idx);
        self.read_idx = end_idx;
        let result: Vec<&DataWithValidity> = if right.len() >= frame_count {
            // No wrap around.
            let (frames, _) = right.split_at(frame_count);
            frames.iter().collect()
        } else {
            // Wrap around.
            let wrapped_frame_count = frame_count - right.len();
            let (wrapped_frames, _) = left.split_at(wrapped_frame_count);
            right.iter().chain(wrapped_frames.iter()).collect()
        };
        result
    }
}

// Counter that wraps around on limit value. E.g., if limit = 3, then the count
// sequence is 0, 1, 2, 0, 1, 2, ...
#[derive(Clone, Debug)]
struct WrapAroundCounter {
    value: usize,
    limit: usize,
}

impl WrapAroundCounter {
    fn new(limit: usize) -> Self {
        assert!(limit > 0);
        Self {
            value: 0,
            limit: limit,
        }
    }

    fn advance(&mut self) {
        self.value = if self.value + 1 == self.limit {
            0
        } else {
            self.value + 1
        };
    }

    fn test(&self) -> bool {
        self.value == 0
    }
}

/// Characteristics of the failures we inject into the simulation.
pub struct FailureProperties {
    /// Probability a frame has one bit corrupted in transit.
    pub frame_corruption_rate: f64,

    /// Random number generator used to calculate probabilities.
    /// Note: the RNG provided by the Default implementation is deterministic.
    pub rng: Box<dyn RngCore>,

    /// Maps node/service name to the metacycle in which we simulate
    /// a crash of that node.
    pub induced_crashes: HashMap<String, usize>,
}

impl Default for FailureProperties {
    /// Default values, assuming no failures; no frame corruption, and no induced crashes.
    /// Note the RNG provided by the Default implementation is deterministic.
    fn default() -> Self {
        Self {
            frame_corruption_rate: 0.0,
            rng: Box::new(Xoshiro256StarStar::seed_from_u64(0x87654321FEDCBA09u64)),
            induced_crashes: HashMap::new(),
        }
    }
}

/// Simulation for HW model
pub struct HardwareSystemSimulation<const BUFFERING: Buffering> {
    /// Simulation link buffers; associated with graph links.
    link_buffers: Vec<LinkBuffer>,

    /// Entry of associated link buffer for a graph link.
    link_buffer_map: HashMap<EdgeIndex, usize>,

    // The simulator local cycles.
    sim_local_cycles: usize,

    /// The simulator frequency, defined as sim_freq = LCM({frequency(x)})
    ///
    /// Example: Let's assume we have three components A, B, C.
    ///
    /// frequency(A) = 100 frequency(B) = 50 frequency(C) = 30
    ///
    /// which implies sim_freq = lcm(100, 50, 30) =  300. For
    /// every 300 ticks of the simulator
    ///
    ///   * node A has ratio frequency(A) : sim_freq = 100 : 300 = 1 : 3, i.e.,
    ///     A ticks once per 3 simulator ticks
    ///   * node B has ratio frequency(B) : sim_freq = 50 : 300 = 1 : 6, i.e., B
    ///     ticks once per 6 simulator ticks
    ///   * likewise node C has ratio 30 : 300 = 1 : 10, i.e., C ticks once per
    ///     10 simulator ticks
    sim_freq: usize,

    /// Simulation counters.
    ///
    /// These counters decide when a node will be runnable. Note that there are
    /// no link simulation counters because links are implicitly stepped by their
    /// endpoints (tx/gather, rx/scatter). They're simply modeled as link buffers
    /// by the simulator to store data transfers in flight.
    ///
    /// Stored in iteration order of `system_spec.iter_nodes()`.
    sim_node_counters: Vec<WrapAroundCounter>,
    sim_link_counters: Vec<WrapAroundCounter>,

    /// A simulation counter to detect the metacycle boundary.
    sim_metacycle_counter: [WrapAroundCounter; BUFFERING],

    /// Characteristics of the failures we inject into the simulation.
    failure_properties: FailureProperties,
}

impl<const BUFFERING: Buffering> HardwareSystemSimulation<BUFFERING> {
    fn sim_cycles_per_metacycle_impl<NS, LS>(
        sim_freq: usize,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
    ) -> [usize; BUFFERING]
    where
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    {
        let node_idx = system_spec.compute_nodes()[0];
        let node_cycles_per_metacycle = system_spec
            .get_node(node_idx)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .cycles_per_metacycle();
        let node_freq = system_spec
            .get_node(node_idx)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .frequency()
            .value;
        node_cycles_per_metacycle.map(|node_cpm| node_cpm * sim_freq / node_freq)
    }

    fn metacycle(&self) -> usize {
        let sim_cpm = self
            .sim_metacycle_counter
            .clone()
            .map(|counter| counter.limit);
        crate::hw::metacycle(self.sim_local_cycles, sim_cpm)
    }

    /// Number of simulator cycles per metacycle, i.e., number of ticks at
    /// frequency HardwareSystemSimulation::sim_freq.
    pub fn sim_cycles_per_metacycle<NS, LS>(
        &self,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
    ) -> [usize; BUFFERING]
    where
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    {
        HardwareSystemSimulation::sim_cycles_per_metacycle_impl(self.sim_freq, system_spec)
    }

    fn all_frequencies<NS, LS>(system_spec: &SystemSpec<BUFFERING, NS, LS>) -> Vec<usize>
    where
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    {
        system_spec
            .iter_nodes()
            .map(|node_id| {
                let node = system_spec.get_node(node_id);
                let node_freq = node
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .frequency()
                    .value;
                let mut freqs = system_spec
                    .get_output_links(node_id)
                    .map(|edge_ref| {
                        system_spec
                            .get_link(edge_ref.id())
                            .into_provisioned_link()
                            .unwrap()
                            .frequency()
                            .value
                    })
                    .collect::<Vec<_>>();
                freqs.push(node_freq);
                freqs
            })
            .flatten()
            .collect::<Vec<_>>()
    }

    fn compute_sim_freq(all_freqs: &Vec<usize>) -> usize {
        all_freqs[1..]
            .iter()
            .fold(all_freqs[0], |accum, x| num::integer::lcm(accum, *x))
    }

    pub fn new<
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + NonFramingLinkTrait + std::fmt::Debug,
    >(
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
        failure_properties: FailureProperties,
    ) -> Self {
        let all_freqs = HardwareSystemSimulation::all_frequencies(system_spec);
        let sim_freq = HardwareSystemSimulation::<BUFFERING>::compute_sim_freq(&all_freqs);

        let mut link_buffer_map = HashMap::<EdgeIndex, usize>::new();
        let mut sim_node_counters = vec![];
        let mut sim_link_counters = vec![];
        let mut link_buffers = vec![];
        for node_idx in system_spec.iter_nodes() {
            let src_node = system_spec.get_node(node_idx);
            let src_node_freq = src_node
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .frequency()
                .value;
            assert!(sim_freq % src_node_freq == 0);
            sim_node_counters.push(WrapAroundCounter::new(sim_freq / src_node_freq));
            for edge_ref in system_spec.get_output_links(node_idx) {
                link_buffer_map.insert(edge_ref.id(), link_buffers.len());
                let link = system_spec.get_link(edge_ref.id());
                let link_freq = link.into_provisioned_link().unwrap().frequency().value;
                link_buffers.push(LinkBuffer::new(
                    1,
                    system_spec.get_link(edge_ref.id()).frame_size(),
                    system_spec.get_link(edge_ref.id()).latency(),
                ));
                assert!(sim_freq % link_freq == 0);
                sim_link_counters.push(WrapAroundCounter::new(sim_freq / link_freq));
            }
        }

        let sim_cpm =
            HardwareSystemSimulation::sim_cycles_per_metacycle_impl(sim_freq, system_spec);
        let sim_metacycle_counter = sim_cpm.map(|sim_cpm| WrapAroundCounter::new(sim_cpm));

        Self {
            link_buffers,
            link_buffer_map,
            sim_local_cycles: 0,
            sim_freq,
            sim_node_counters,
            sim_link_counters,
            sim_metacycle_counter,
            failure_properties: failure_properties,
        }
    }

    /// Step scatterers of the provided node index.
    fn simulate_link_scatter<
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    >(
        &mut self,
        node_id: NodeIndex,
        link_id: EdgeIndex,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
        callbacks: OptionSimCallbacks,
    ) {
        let node_name = system_spec.get_node(node_id).borrow().name().to_owned();
        let node_crashed = system_spec
            .get_node(node_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .get_crashed();
        log::trace!(
            "Stepping link rx node name: {} id: {:?} edge: {:?} @cycle {}",
            &node_name,
            node_id,
            link_id,
            self.sim_local_cycles
        );
        // Step a link (the comms), i.e., the gather+scatter pairs that comprise the link end-points.
        let (_, link_dst) = system_spec.get_link_endpoints(link_id);
        let dst_node_id = link_dst;
        assert_eq!(node_id, dst_node_id);
        let dst_node = system_spec.get_node(node_id);
        let mut prov_dst_ref = dst_node.borrow_mut();
        let prov_dst = prov_dst_ref
            .into_mut_provisioned_node()
            .expect("Expected provisioned destination.");

        let link_buffer_idx = *self
            .link_buffer_map
            .get(&link_id)
            .expect("Simulator link buffer map invalid.");
        let link_buffer = &mut self.link_buffers[link_buffer_idx];
        let inputs = link_buffer
            .read_frames(1)
            .iter()
            .map(|frame| if frame.valid { Some(&frame.data) } else { None })
            .collect::<Vec<_>>();
        if node_crashed {
            // Note: We need to still call link_buffer.read_frames() to empty
            // the link even if this node has crashed, so that any write_frame()
            // calls on the other side of this link don't fail assertions about
            // the link not being full.
            return;
        }
        prov_dst
            .step_scatter(
                system_spec.get_link(link_id).dst_port(),
                inputs.as_slice(),
                callbacks,
            )
            .map_err(|e| {
                panic!(
                    "Run failed for node {:?} link {:?} scatter with error {:?}",
                    node_id, link_id, e
                );
            })
            .unwrap();
        log::trace!("Stepped link rx {:?} {:?}", link_id, inputs);
    }

    /// Step gatherers of the provided node index.
    fn simulate_link_gather<
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    >(
        &mut self,
        node_id: NodeIndex,
        link_id: EdgeIndex,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
        callbacks: OptionSimCallbacks,
    ) {
        let node_name = system_spec.get_node(node_id).borrow().name().to_owned();
        let node_crashed = system_spec
            .get_node(node_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .get_crashed();
        log::trace!(
            "Stepping link tx node name: {} id: {:?} edge id: {:?} @cycle {} crashed: {}",
            node_name,
            node_id,
            link_id,
            self.sim_local_cycles,
            system_spec
                .get_node(node_id)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .get_crashed(),
        );
        // Step a link (the comms), i.e., the gather+scatter pairs that comprise the link end-points.
        let link = system_spec.get_link(link_id);
        let src_node = system_spec.get_node(node_id);
        let (link_src, _) = system_spec.get_link_endpoints(link_id);
        assert_eq!(link_src, node_id);
        let mut prov_src_ref = src_node.borrow_mut();
        let prov_src = prov_src_ref
            .into_mut_provisioned_node()
            .expect("Expected provisioned source.");
        let link_buffer_idx = *self
            .link_buffer_map
            .get(&link_id)
            .expect("Simulator link buffer map invalid.");
        let link_buffer = &mut self.link_buffers[link_buffer_idx];
        let frames_per_cycle = 1;
        let mut outputs = link_buffer.write_frames(frames_per_cycle);
        if node_crashed {
            // Note: We need to call write_frames() on the link buffer even
            // when the node has crashed, so that any corresponding
            // read_frames() calls in simulate_link_scatter() don't fail
            // assertions about there being a frame on the link that it can
            // read.
            return;
        }
        prov_src
            .step_gather(link.src_port(), &mut outputs.as_mut_slice(), callbacks)
            .map_err(|e| {
                panic!(
                    "Run failed for node {:?} link {:?} gather with error {:?}",
                    node_id, link_id, e
                );
            })
            .unwrap();

        // If the simulation specified a random frame corruption rate,
        // randomly mess with with transmitted bits.
        if self.failure_properties.frame_corruption_rate > 0.0 {
            for frame in outputs.iter_mut().filter(|f| f.valid) {
                if self
                    .failure_properties
                    .rng
                    .gen_bool(self.failure_properties.frame_corruption_rate)
                {
                    log::info!(
                        "Randomly injecting frame corruption; node name: {} edge id: {:?} @cycle {}",
                        node_name,
                        link_id,
                        self.sim_local_cycles
                    );
                    let idx = self.failure_properties.rng.gen_range(0..frame.data.len());
                    let bit = frame.data[idx];
                    frame.data.as_mut_bitslice().set(idx, !bit);
                }
            }
        }

        log::trace!("Stepped link tx {:?} {:?}", link_id, outputs);
    }

    fn induce_crashes<
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + Clone + std::fmt::Debug,
    >(
        &mut self,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
    ) {
        if self.failure_properties.induced_crashes.is_empty() {
            // No simulated crashes to induce!
            return;
        }

        let metacycle_now = self.metacycle();
        for (node_name, &crash_at_cycle) in self.failure_properties.induced_crashes.iter() {
            if crash_at_cycle != metacycle_now {
                continue;
            }
            // Node crashed in this metacycle.
            let node_index = system_spec.get_node_index_by_name(node_name).unwrap();
            log::trace!(
                "Simulating crash of node {}/{} at cycle {} metacycle {}",
                node_name,
                node_index.index(),
                self.sim_local_cycles,
                self.metacycle()
            );

            system_spec
                .get_node(node_index)
                .borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_crashed(true);

            // Mark the outgoing links units as down; set the gather units
            // on this node as down, and set the scatter units on the
            // receiving nodes as down.
            for edge_ref in system_spec.get_output_links(node_index) {
                let link = system_spec.get_link(edge_ref.id());
                let (_, dst_id) = system_spec.get_link_endpoints(edge_ref.id());
                system_spec
                    .get_node(dst_id)
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_scatter_link_status(link.dst_port(), LinkStatus::Down);

                system_spec
                    .get_node(node_index)
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_gather_link_status(link.src_port(), LinkStatus::Down);
            }

            // Mark the incoming link links as down; set our scatter units
            // as down, and the peer gather units on the other side.
            for edge_ref in system_spec.get_input_links(node_index) {
                let link = system_spec.get_link(edge_ref.id());
                let (src_id, _) = system_spec.get_link_endpoints(edge_ref.id());
                system_spec
                    .get_node(src_id)
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_gather_link_status(link.src_port(), LinkStatus::Down);

                system_spec
                    .get_node(node_index)
                    .borrow_mut()
                    .into_mut_provisioned_node()
                    .unwrap()
                    .set_scatter_link_status(link.dst_port(), LinkStatus::Down);
            }
        }
    }

    /// Step compute of the provided node index.
    fn simulate_node_compute<
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    >(
        &mut self,
        node_idx: usize,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
        callbacks: OptionSimCallbacks,
    ) {
        let graph_node_idx = NodeIndex::new(node_idx);
        let node_name = system_spec
            .get_node(graph_node_idx)
            .borrow()
            .name()
            .to_string();
        log::trace!(
            "Running Compute for node name: \"{}\" id: {} @cycle {}",
            node_name,
            node_idx,
            self.sim_local_cycles
        );
        let inputs = vec![];
        let mut outputs = vec![];
        system_spec
            .get_node(graph_node_idx)
            .borrow_mut()
            .step(&inputs, &mut outputs, callbacks)
            .map_err(|e| {
                panic!(
                    "Run failed for node {} name: \"{}\" with error {:?}",
                    node_idx, node_name, e
                );
            })
            .unwrap();
    }
}

// application-level behavioral simulation;  assumes sufficient resources have been allocated for
// all nodes and links;  does _not_ model any node-internal resource usage (compute
// microarchitecture usage or compute memory);  _does_ model communication memory;  _does_ model
// relative timing at the application-level but not against wall-clock time and hence this
// simulation is insufficient for demonstrating wall-clock performance (again, this simulation
// simply assumes sufficiently powerful and plentiful resources exist to meet application needs)
pub struct SoftwareSystemSimulation {
    // all nodes in the system; the set of s and their frequencies are fixed once the
    // simulation is created (hence the boxed slice)
    nodes: Box<[Node]>,

    /// the topology visitor;
    ///
    /// a visitor that traverses the nodes in the correct serialization order for a metacycle.
    /// we store it here because we only need to compute serialization once
    /// since our graphs are frozen; for simulations, we reset and visit
    /// again.
    visitor: MetacycleVisitor,
}

#[derive(Default)]
pub struct SystemSimulationCallbacks {
    vcd_writer: Option<Rc<RefCell<VcdWriter>>>,
}

impl SystemSimulationCallbacks {
    pub fn get_vcd_writer(&mut self) -> Option<Rc<RefCell<VcdWriter>>> {
        match &self.vcd_writer {
            Some(writer) => Some(Rc::clone(&writer)),
            None => None,
        }
    }

    pub fn create_vcd_callbacks() -> Self {
        Self {
            vcd_writer: Some(Rc::new(RefCell::new(VcdWriter::default()))),
        }
    }

    pub fn vcd<F>(&mut self, f: F)
    where
        F: FnOnce(Rc<RefCell<VcdWriter>>),
    {
        self.get_vcd_writer().map(|writer| f(writer));
    }
}

pub type OptionSimCallbacks<'a> = &'a mut SystemSimulationCallbacks;

impl<const BUFFERING: Buffering> SystemSimulationTrait<BUFFERING>
    for HardwareSystemSimulation<BUFFERING>
{
    fn sim_type(&self) -> SimulationType {
        SimulationType::Hardware
    }

    // step the entire system one cycle (one unit of root frequency), which will correspond to
    // multiple cycles for nodes operating at faster frequencies than the root
    fn simulate_system_one_cycle<
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + Clone + std::fmt::Debug,
    >(
        &mut self,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
        callbacks: OptionSimCallbacks,
    ) {
        let sim_cpm = self.sim_cycles_per_metacycle(system_spec);
        log::trace!(
            "simulate_system_one_cycle, sim cycle: {}, sim frequency: {}, sim cpm: {:?}",
            self.sim_local_cycles,
            self.sim_freq,
            sim_cpm,
        );
        log::trace!("sim node counters: {:#?}", self.sim_node_counters);
        log::trace!("sim link counters: {:#?}", self.sim_link_counters);
        self.induce_crashes(system_spec);
        let _vcd_trace_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(writer, DEFAULT_TOP_MODULE));
        callbacks.vcd(|writer| {
            writer.borrow_mut().enter_cycle();
        });
        // Comms: step all system gathers (fills link buffer data), and
        // subsequently step all system scatters (drains link buffer data).
        let mut link_counter_idx = 0;
        for node_id in system_spec.iter_nodes() {
            for edge_ref in system_spec.get_output_links(node_id) {
                if self.sim_link_counters[link_counter_idx].test() {
                    self.simulate_link_gather(node_id, edge_ref.id(), system_spec, callbacks);
                }
                link_counter_idx += 1;
            }
        }
        link_counter_idx = 0;
        // Note: we need to iterate in node, then *output link* iteration order, because
        // our link counters are stored in that order.
        for node_id in system_spec.iter_nodes() {
            for edge_ref in system_spec.get_output_links(node_id) {
                if self.sim_link_counters[link_counter_idx].test() {
                    let (_, dst_node_id) = system_spec.get_link_endpoints(edge_ref.id());
                    self.simulate_link_scatter(dst_node_id, edge_ref.id(), system_spec, callbacks);
                }
                link_counter_idx += 1;
            }
        }

        // Compute
        for (i, node_id) in system_spec.iter_nodes().enumerate() {
            if self.sim_node_counters[i].test() {
                self.simulate_node_compute(node_id.index(), system_spec, callbacks);
            }
        }
        // Finally advance node and link counters.
        for i in 0..self.sim_node_counters.len() {
            self.sim_node_counters[i].advance();
        }
        for i in 0..self.sim_link_counters.len() {
            self.sim_link_counters[i].advance();
        }
        let metacycle = self.metacycle();
        self.sim_metacycle_counter[metacycle % self.sim_metacycle_counter.len()].advance();
        self.sim_local_cycles += 1;
        callbacks.vcd(|writer| {
            writer
                .borrow_mut()
                .change_vector_immediately("sim_cycles", self.sim_local_cycles as u64);
        });
        // After all nodes have been cycled, advance marked nodes to the next metacycle.
        if self.sim_local_cycles > 0
            && self.sim_metacycle_counter[metacycle % self.sim_metacycle_counter.len()].test()
        // use metacycle prior to local_cycles being updated
        {
            log::trace!("advancing metacycles: (prev) local_cycle: {} (prev) metacycle: {} (next) local_cycles: {}, (next) metacycle: {}", self.sim_local_cycles - 1, metacycle, self.sim_local_cycles, self.metacycle());
            for node_idx in system_spec.iter_nodes() {
                let node = system_spec.get_node(node_idx);
                let mut prov_node_ref = node.borrow_mut();
                let prov_node = prov_node_ref
                    .into_mut_provisioned_node()
                    .expect("Expected provisioned node in mapped system spec.");
                if !prov_node.get_crashed() {
                    prov_node.advance_metacycle();
                }
            }
        }
        callbacks.vcd(|writer| {
            writer.borrow_mut().end_cycle();
        });
    }
}

impl SoftwareSystemSimulation {
    pub fn new<
        NS: NodeSpec<{ APPLICATION_NODE }> + ApplicationNode + std::fmt::Debug,
        LS: LinkSpec + FramingLinkTrait + std::fmt::Debug,
    >(
        system_spec: &SystemSpec<APPLICATION_NODE, NS, LS>,
    ) -> Self {
        assert!(
            !system_spec.is_empty(),
            "systems must contain at least one node"
        );

        system_spec.normalize_frequencies();

        // TODO(cascaval): should we generate these using into_nodes_edges()
        // for a clone of the graph?
        let mut nodes = Vec::new();
        for (i, node_id) in system_spec.iter_nodes().enumerate() {
            nodes.push(Node::new_framing(node_id, system_spec));
            assert_eq!(i, node_id.index());
        }

        // TODO(tammo): assert the node graph is connected (not disjoint)
        Self {
            nodes: nodes.into_boxed_slice(),
            visitor: MetacycleVisitor::new(&system_spec.topo),
        }
    }

    // step a single node for one local cycle (as defined by its frequency)
    fn simulate_node_one_cycle<
        const BUFFERING: Buffering,
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    >(
        &mut self,
        target_node_idx: usize,
        system_spec: &SystemSpec<BUFFERING, NS, LS>,
        callbacks: OptionSimCallbacks,
    ) {
        log::trace!(
            "Simulating node name: {} id: {}",
            system_spec
                .get_node(NodeIndex::new(target_node_idx))
                .borrow()
                .name(),
            target_node_idx
        );
        let (left, rest) = self.nodes.split_at_mut(target_node_idx);
        let (target_node, right) = rest.split_first_mut().unwrap();
        let sys_target_node_idx = target_node.node_index;
        let outputs = target_node
            .outputs
            .iter_mut()
            .map(|o| o.get_next_src_frames())
            .flatten()
            .zip(
                system_spec
                    .get_output_links(sys_target_node_idx)
                    .map(|edge| edge.weight().src_port().frame_size()),
            )
            .collect::<Vec<(OutputFrameRef, usize)>>();
        let terminations = &mut target_node.terminations;
        let inputs = target_node
            .inputs
            .iter()
            .enumerate()
            .flat_map(|(input_idx, link_handle)| {
                assert_ne!(link_handle.src_idx.index(), target_node_idx);
                let neighbor = {
                    if link_handle.src_idx.index() < target_node_idx {
                        &left[link_handle.src_idx.index()]
                    } else {
                        &right[link_handle.src_idx.index() - (target_node_idx + 1)]
                    }
                };
                let src_port: usize = link_handle.src_port.into();
                let link = &neighbor.outputs[src_port];
                let termination = &mut terminations[input_idx];
                link.get_next_dst_frames(termination)
                    .iter()
                    .map(|frame| {
                        if frame.valid {
                            (Some(&frame.data), link_handle.src_port.frame_size())
                        } else {
                            (None, link_handle.src_port.frame_size())
                        }
                    })
                    .collect::<Vec<(InputFrameRef, usize)>>()
            })
            .collect::<Vec<(InputFrameRef, usize)>>();
        callbacks.vcd(|writer| {
            let _vcd_node_scope = VcdWriter::managed_trace_scope(
                Rc::clone(&writer),
                system_spec.get_node(sys_target_node_idx).borrow().name(),
            );
            for (i, (frame_ref, frame_size)) in inputs.iter().enumerate() {
                let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
                writer.borrow_mut().change_input_frame_ref(
                    "input",
                    *frame_ref,
                    *frame_size,
                    ChangeValue::Immediately,
                );
            }
        });
        let inputs = inputs.iter().map(|inp| inp.0).collect::<Vec<_>>();
        // TODO: Support mocking failed links in software simulation.
        let input_links = inputs
            .iter()
            .map(|_| LinkProperties {
                status: LinkStatus::Up,
            })
            .collect::<Vec<_>>();
        let output_links = outputs
            .iter()
            .map(|_| LinkProperties {
                status: LinkStatus::Up,
            })
            .collect::<Vec<_>>();
        let sys_call_context = MockSystemContext::new(input_links, output_links);
        let (mut output_refs, output_frame_sizes): (Vec<_>, Vec<_>) = outputs.into_iter().unzip();
        system_spec
            .get_node(sys_target_node_idx)
            .borrow_mut()
            .into_mut_application_node()
            .expect("Should be application node")
            .run_action_function(&inputs, &mut output_refs, callbacks, &sys_call_context)
            .map_err(|e| {
                panic!("Run failed for node {} with error {:?}", target_node_idx, e);
            })
            .unwrap();
        callbacks.vcd(|writer| {
            let _vcd_node_scope = VcdWriter::managed_trace_scope(
                Rc::clone(&writer),
                system_spec.get_node(sys_target_node_idx).borrow().name(),
            );
            for (i, (output_ref, frame_size)) in
                output_refs.iter().zip(output_frame_sizes).enumerate()
            {
                let _vcd_i_scope = VcdWriter::managed_trace_scope(Rc::clone(&writer), &i);
                writer.borrow_mut().change_output_frame_ref(
                    "output",
                    *output_ref,
                    frame_size,
                    ChangeValue::Defer,
                );
            }
        });
    }
}

impl SystemSimulationTrait<{ APPLICATION_NODE }> for SoftwareSystemSimulation {
    fn sim_type(&self) -> SimulationType {
        SimulationType::Software
    }

    // step the entire system one cycle (one unit of root frequency), which will correspond to
    // multiple cycles for nodes operating at faster frequencies than the root
    fn simulate_system_one_cycle<
        NS: NodeSpec<{ APPLICATION_NODE }> + std::fmt::Debug,
        LS: LinkSpec + std::fmt::Debug,
    >(
        &mut self,
        system_spec: &SystemSpec<{ APPLICATION_NODE }, NS, LS>,
        callbacks: OptionSimCallbacks,
    ) {
        let _vcd_trace_scope = callbacks
            .get_vcd_writer()
            .map(|writer| VcdWriter::managed_trace_scope(writer, DEFAULT_TOP_MODULE));
        callbacks.vcd(|writer| {
            writer.borrow_mut().enter_cycle();
        });
        self.visitor.reset();
        while let Some(node_id) = self.visitor.next() {
            self.simulate_node_one_cycle(node_id.index(), system_spec, callbacks);
        }
        callbacks.vcd(|writer| {
            writer.borrow_mut().end_cycle();
        });
    }
}

// private within this module, track the dst state for a link; this struct is located with the dst
// node for the link because only that node is mutable when being stepped; the fields match those
// for their src equivalents, which are documented with the Link struct
#[derive(Clone, Copy, Debug)]
struct LinkTermination {
    dst_frames_idx: usize,
    follower_batch_cycle_progress: usize,
    dst_frames_read: i64,
}

// private within this module, node simulation data
struct Node {
    node_index: NodeIndex,

    outputs: Box<[Link]>,
    inputs: Box<[EdgeProxy]>,
    terminations: Box<[LinkTermination]>,
}

impl Node {
    /// Framing variant using Links that conform to a notion of framing - to be obsoleted.
    fn new_framing<
        const BUFFERING: Buffering,
        NS: NodeSpec<BUFFERING> + std::fmt::Debug,
        LS: LinkSpec + FramingLinkTrait + std::fmt::Debug,
    >(
        node: NodeIndex,
        spec: &SystemSpec<BUFFERING, NS, LS>,
    ) -> Self {
        // TODO(cascaval): write a topology consistency checker rather than
        // having checks done throughout the code.

        // Note: the edge iterators do not necessarily return edges in the order of their ports.
        // TODO(cascaval): it seems there are places in the code where we
        // depend on this order. This was one of them. Need to ensure that
        // either we build that kind of an ordered iterator, or we ensure we
        // do not build in this assumption in the code.
        let (n_inputs, n_outputs) = spec.get_node_inout_count(node);
        let mut outputs = vec![Link::empty(); n_outputs];
        for edge in spec.get_output_links(node) {
            let src_port: usize = edge.weight().src_port().into();
            outputs[src_port] = Link::new(edge.weight());
        }
        let mut inputs = vec![
            EdgeProxy {
                src_port: Port::default(),
                src_idx: NodeIndex::new(0),
            };
            n_inputs
        ];
        let mut terminations = vec![
            LinkTermination {
                dst_frames_idx: 0,
                follower_batch_cycle_progress: 0,
                dst_frames_read: 0,
            };
            n_inputs
        ];
        for edge in spec.get_input_links(node) {
            let dst_port: usize = edge.weight().dst_port().into();
            inputs[dst_port] = EdgeProxy {
                src_port: edge.weight().src_port(),
                src_idx: spec.get_link_endpoints(edge.id()).0,
            };
            terminations[dst_port] = LinkTermination {
                // dst is set to one batch ahead of src; src and dst can
                // each fill a full batch each root cycle; this ensures that
                // no corruption occurs provided that each side is stepped
                // only the appropriate number of times each root cycle
                dst_frames_idx: edge.weight().follower_batch_size(),
                follower_batch_cycle_progress: 0,
                dst_frames_read: 0,
            };
        }

        Self {
            node_index: node,
            outputs: outputs.into_boxed_slice(),
            inputs: inputs.into_boxed_slice(),
            terminations: terminations.into_boxed_slice(),
        }
    }
}

// private within this module; captures topology edge info that is required
// to dereference input links.
#[derive(Clone, Debug)]
struct EdgeProxy {
    src_port: Port,
    src_idx: NodeIndex,
}

// private within this module, simulation-implementation of inter-node data connectivity
// we need clone only for vec.resize().
#[derive(Clone, Debug)]
struct Link {
    // circular buffer of frames, fully occupied, representing data on the wire and in IO buffers on
    // both sides
    frames: Box<[DataWithValidity]>,

    // the frames circular buffer has a batch of frames being written to starting at src_frames_idx
    // and another batch being read from starting at dst_frames_idx; the dst_frames_idx is tracked
    // via LinkTerminationData at the dst node because only that node (the one being stepped) is
    // mutable during per-cycle link processing
    //
    // the lead side processes batches of just one frame per local cycle while the follower side
    // might have larger batches which take multiple cycles to process; simulation needs to ensure
    // that neither side overruns the other (which would cause incorrect results -- data corruption)
    //
    // reads (dst) should logically always remain just ahead of writes (src), such that reads
    // consume the whole circular buffer prior to consuming the most recently written data
    src_frames_idx: usize,

    // for debugging
    src_frames_written: i64,

    // these are copies of the LinkSpec; would be nice to just use the spec,
    // but storing a reference to a dynamic object is challenging.
    // TODO: Switch to storing the LinkSpec as Rc<RefCell<_>>.

    // the framing lead
    framing_lead: FramingLead,

    // for the follower side, the size of the batch
    follower_batch_size: usize,

    // for the follower side, the number of cycles per batch
    follower_batch_cycles: usize,

    // for the follower side, a count of progress through follower_batch_cycles
    follower_batch_cycle_progress: usize,
}

impl Link {
    fn new<LS: LinkSpec + FramingLinkTrait + std::fmt::Debug>(spec: &LS) -> Self {
        // lead_ratio * latency frames on the wire; lead_ratio in buffers on each side (the lead
        // side strictly needs only a single frame in memory, but the extra frames are necessary to
        // make the link have integer end-to-end latency (must contain and integer multiple of
        // lead_ratio frame batches); spec.follower_batch_size == lead_ratio
        let frame_count = (spec.latency().0 + 2) * spec.follower_batch_size();
        let frames: Vec<DataWithValidity> = (0..frame_count)
            .map(|_| DataWithValidity {
                data: BitVec::repeat(false, spec.frame_size()).into_boxed_bitslice(),
                valid: false,
            })
            .collect();
        Self {
            frames: frames.into_boxed_slice(),
            src_frames_idx: 0,
            framing_lead: spec.framing_lead(),
            follower_batch_size: spec.follower_batch_size(),
            follower_batch_cycles: spec.follower_batch_cycles(),
            follower_batch_cycle_progress: 0,
            src_frames_written: 0,
        }
    }

    // return an placeholder
    fn empty() -> Self {
        Self {
            frames: vec![DataWithValidity {
                data: bitvec![0; 1].into_boxed_bitslice(),
                valid: false,
            }]
            .into_boxed_slice(),
            src_frames_idx: 0,
            framing_lead: FramingLead::Src,
            follower_batch_size: 0,
            follower_batch_cycles: 0,
            follower_batch_cycle_progress: 0,
            src_frames_written: 0,
        }
    }

    // calculate the next index location (with incr offset) around the circular frames buffer
    fn idx_incr(&self, idx: usize, incr: usize) -> usize {
        (idx + incr) % self.frames.len()
    }

    // returns mutable references for the current set frames for writing data into this link; update
    // of src_frames_idx (if needed) happens prior to calculating the frame references (with
    // opposite behavior for dst_frames_idx this allows for zero-latency links)
    fn get_next_src_frames(&mut self) -> Vec<&mut DataWithValidity> {
        trace!(
            "get_next_src_frames src_idx: {}, src_count: {}",
            self.src_frames_idx,
            self.src_frames_written
        );
        let start_idx = self.src_frames_idx;
        // update now because doing so at the end is not practical wrt borrow checker; but
        // importantly the indices for the frames being returned are the pre-increment ones
        match self.framing_lead {
            FramingLead::Src => {
                self.src_frames_idx = self.idx_incr(self.src_frames_idx, 1);
                self.src_frames_written += 1;
            }
            FramingLead::Dst => {
                self.follower_batch_cycle_progress += 1;
                if self.follower_batch_cycle_progress == self.follower_batch_cycles {
                    self.follower_batch_cycle_progress = 0;
                    self.src_frames_idx =
                        self.idx_incr(self.src_frames_idx, self.follower_batch_size);
                    self.src_frames_written += self.follower_batch_size as i64;
                }
            }
        };
        let frame_count = match self.framing_lead {
            FramingLead::Src => 1,
            FramingLead::Dst => self.follower_batch_size,
        };
        let (left, right) = self.frames.split_at_mut(start_idx);
        if right.len() >= frame_count {
            let (frames, _) = right.split_at_mut(frame_count);
            frames.iter_mut().collect()
        } else {
            let wrapped_frame_count = frame_count - right.len();
            let (wrapped_frames, _) = left.split_at_mut(wrapped_frame_count);
            right.iter_mut().chain(wrapped_frames.iter_mut()).collect()
        }
    }

    // returns immutable references for the current set frames for reading data from this link;
    // update of dst_frames_idx (if needed) happens after to calculating the frame references (with
    // opposite behavior for src_frames_idx this allows for zero-latency links); because self cannot
    // be mutably referenced (this function is called from a context that precludes doing so), the
    // necessary mutable state is located with the dst node and passed separately via
    // LinkTermination
    fn get_next_dst_frames(&self, termination: &mut LinkTermination) -> Vec<&DataWithValidity> {
        let frame_count = match self.framing_lead {
            FramingLead::Src => self.follower_batch_size,
            FramingLead::Dst => 1,
        };
        trace!(
            "get_next_dst_frames src_idx: {}, src_count: {}, dst_idx: {}, dst_count: {}",
            self.src_frames_idx,
            self.src_frames_written,
            termination.dst_frames_idx,
            termination.dst_frames_read
        );
        assert!(
            (self.src_frames_written - termination.dst_frames_read).abs() as usize
                <= self.follower_batch_size,
            "link frame storage src-dst mis-aligned for {:?} {:?}",
            self.src_frames_written,
            termination.dst_frames_read
        );
        let (left, right) = self.frames.split_at(termination.dst_frames_idx);
        let result: Vec<&DataWithValidity> = if right.len() >= frame_count {
            let (frames, _) = right.split_at(frame_count);
            frames.iter().collect()
        } else {
            let wrapped_frame_count = frame_count - right.len();
            let (wrapped_frames, _) = left.split_at(wrapped_frame_count);
            right.iter().chain(wrapped_frames.iter()).collect()
        };
        match self.framing_lead {
            FramingLead::Src => {
                termination.follower_batch_cycle_progress += 1;
                if termination.follower_batch_cycle_progress == self.follower_batch_cycles {
                    termination.follower_batch_cycle_progress = 0;
                    termination.dst_frames_idx =
                        self.idx_incr(termination.dst_frames_idx, self.follower_batch_size);
                    termination.dst_frames_read += self.follower_batch_size as i64;
                }
            }
            FramingLead::Dst => {
                termination.dst_frames_idx = self.idx_incr(termination.dst_frames_idx, 1);
                termination.dst_frames_read += 1;
            }
        };
        result
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::specs::SystemSpec;
    use crate::PortProperties;
    use crate::Service;
    use bits::*;

    #[derive(Clone, Debug)]
    struct TestLink {
        src_port: Port,
        dst_port: Port,
        latency: Latency,
        frame_size: usize,
        framing_lead: FramingLead,
        follower_batch_size: usize,
        follower_batch_cycles: usize,
    }

    impl TestLink {
        pub fn new(
            src_port_idx: usize,
            dst_port_idx: usize,
            latency: Latency,
            frame_size: usize,
        ) -> Self {
            Self {
                src_port: Port::new(
                    src_port_idx,
                    &PortProperties {
                        direction: Direction::Outgoing,
                        frame_size: frame_size.into(),
                        ..Default::default()
                    },
                ),
                dst_port: Port::new(
                    dst_port_idx,
                    &PortProperties {
                        direction: Direction::Incoming,
                        frame_size: frame_size.into(),
                        ..Default::default()
                    },
                ),
                latency,
                frame_size,
                framing_lead: FramingLead::Src,
                follower_batch_size: 0,
                follower_batch_cycles: 0,
            }
        }
    }

    impl LinkSpec for TestLink {
        fn src_port(&self) -> Port {
            self.src_port
        }
        fn dst_port(&self) -> Port {
            self.dst_port
        }
        fn latency(&self) -> Latency {
            self.latency
        }
        fn set_latency(&mut self, latency: Latency) {
            self.latency = latency;
        }
        fn get_ports(&self) -> (Port, Port) {
            (self.src_port, self.dst_port)
        }
        fn frame_size(&self) -> usize {
            self.frame_size
        }
    }

    impl FramingLinkTrait for TestLink {
        fn framing_lead(&self) -> FramingLead {
            self.framing_lead
        }

        fn follower_batch_size(&self) -> usize {
            self.follower_batch_size
        }
        fn follower_batch_cycles(&self) -> usize {
            self.follower_batch_cycles
        }
        fn set_framing(
            &mut self,
            framing_lead: FramingLead,
            lead_framing: FrequencyFactor,
            follower_framing: FrequencyFactor,
        ) {
            self.framing_lead = framing_lead;
            self.follower_batch_size = lead_framing.0;
            self.follower_batch_cycles = follower_framing.0;
        }
    }

    // Specialized specification for a hybrid system that allows us to test
    // the functionality implemented in the simulator, which just moves data
    // on links. This combines Service nodes to model just calling an action
    // function, with hardware links that support various latencies.
    type TestSpec = SystemSpec<{ APPLICATION_NODE }, Service, TestLink>;

    #[track_caller]
    fn print_args(
        loopback: &LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
    ) {
        let empty = bits![];
        print!(
            "loopback: {}",
            if loopback.is_some() {
                loopback.as_ref().unwrap().as_bitslice()
            } else {
                empty
            }
        );
        print!("  inputs: ");
        for x in inputs {
            print!(
                "{} ",
                if x.is_some() {
                    x.unwrap().as_bitslice()
                } else {
                    empty
                }
            );
        }
        print!(" outputs: ");
        for x in outputs {
            print!("{},{} ", x.data.as_bitslice(), x.valid);
        }
        println!();
    }

    // action where output[0] = input[0] + 1; or zero if no valid input; and it counts cycles on
    // the loopback if one exists
    #[track_caller]
    fn simple_action(
        loopback: LoopbackRef,
        inputs: &[InputFrameRef],
        outputs: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        let mut output: u8 = 0;
        if let Some(data) = inputs[0] {
            output = u8::unpack(data.as_bitslice()) + 1;
        }
        output.pack_to(&mut outputs[0].data);
        outputs[0].valid = true;
        print_args(&loopback, inputs, outputs);
        if let Some(mut data) = loopback {
            let value = u8::unpack(data.as_bitslice()) + 1;
            value.pack_to(&mut data);
        }
    }

    #[test]
    fn test_matched_frequencies() {
        let packed_persistent_state = u8::pack(&0).into_boxed_bitslice();
        let mut system_spec = TestSpec::new();
        let svc_a = Service::new(
            "svc_a",
            simple_action,
            Some(packed_persistent_state.clone()),
            FrequencyFactor(1),
        );
        let svc_b = Service::new(
            "svc_b",
            simple_action,
            Some(packed_persistent_state.clone()),
            FrequencyFactor(1),
        );
        let na = system_spec.add_node(svc_a);
        let nb = system_spec.add_node(svc_b);
        let l1 = TestLink::new(0, 0, Latency(0), 8);
        let l2 = TestLink::new(0, 0, Latency(0), 8);
        system_spec.link_simplex_framing(na, nb, l1, FramingLead::Src);
        system_spec.link_simplex_framing(nb, na, l2, FramingLead::Dst);
        // system_spec.link_duplex(&svc_a, 0, 0, &svc_b, 0, 0, 8, 8, Latency(0));
        let mut simulation = SoftwareSystemSimulation::new(&mut system_spec);
        for _ in 0..5 {
            simulation.simulate_system_one_cycle(
                &mut system_spec,
                &mut SystemSimulationCallbacks::default(),
            );
        }
        // both nodes operate on single frames each cycle
        let c = &simulation.nodes[0].outputs[0];
        assert_eq!(2, c.frames.len());
        assert_eq!(5, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(3, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
        let c = &simulation.nodes[1].outputs[0];
        assert_eq!(2, c.frames.len());
        assert_eq!(5, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(3, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
    }

    #[test]
    fn test_faster_dom() {
        let mut system_spec = TestSpec::new();
        let svc_a = Service::new("svc_a", simple_action, None, FrequencyFactor(2));
        let svc_b = Service::new("svc_b", simple_action, None, FrequencyFactor(6));
        let na = system_spec.add_node(svc_a);
        let nb = system_spec.add_node(svc_b);
        let l = TestLink::new(0, 0, Latency(0), 8);
        system_spec.link_simplex_framing(na, nb, l.clone(), FramingLead::Dst);
        system_spec.link_simplex_framing(nb, na, l.clone(), FramingLead::Src);

        // system_spec.link_duplex(&svc_b, 0, 0, &svc_a, 0, 0, 8, 8, Latency(0));
        let mut simulation = SoftwareSystemSimulation::new(&mut system_spec);
        for _ in 0..5 {
            simulation.simulate_system_one_cycle(
                &mut system_spec,
                &mut SystemSimulationCallbacks::default(),
            );
        }
        // node 0 operates on 3 frames at once (in and out), only setting valid on the first output;
        // node 1 operates on only individual frames (3x faster), setting valid on all outputs
        let c = &simulation.nodes[0].outputs[0];
        assert_eq!(6, c.frames.len());
        assert_eq!(15, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(false, c.frames[1].valid);
        assert_eq!(0, u8::unpack(c.frames[2].data.as_bitslice()));
        assert_eq!(false, c.frames[2].valid);
        assert_eq!(3, u8::unpack(c.frames[3].data.as_bitslice()));
        assert_eq!(true, c.frames[3].valid);
        assert_eq!(0, u8::unpack(c.frames[4].data.as_bitslice()));
        assert_eq!(false, c.frames[4].valid);
        assert_eq!(0, u8::unpack(c.frames[5].data.as_bitslice()));
        assert_eq!(false, c.frames[5].valid);
        let c = &simulation.nodes[1].outputs[0];
        assert_eq!(6, c.frames.len());
        assert_eq!(15, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
        assert_eq!(0, u8::unpack(c.frames[2].data.as_bitslice()));
        assert_eq!(true, c.frames[2].valid);
        assert_eq!(3, u8::unpack(c.frames[3].data.as_bitslice()));
        assert_eq!(true, c.frames[3].valid);
        assert_eq!(0, u8::unpack(c.frames[4].data.as_bitslice()));
        assert_eq!(true, c.frames[4].valid);
        assert_eq!(0, u8::unpack(c.frames[5].data.as_bitslice()));
        assert_eq!(true, c.frames[5].valid);
    }

    #[test]
    fn test_faster_lead_primes() {
        let _logger = env_logger::builder().is_test(true).try_init();

        let mut system_spec = TestSpec::new();
        let svc_a = Service::new("svc_a", simple_action, None, FrequencyFactor(5));
        let svc_b = Service::new("svc_b", simple_action, None, FrequencyFactor(7));
        let na = system_spec.add_node(svc_a);
        let nb = system_spec.add_node(svc_b);
        let l = TestLink::new(0, 0, Latency(0), 8);
        system_spec.link_simplex_framing(nb, na, l.clone(), FramingLead::Src);
        system_spec.link_simplex_framing(na, nb, l.clone(), FramingLead::Dst);
        // system_spec.link_duplex(&svc_b, 0, 0, &svc_a, 0, 0, 8, 8, Latency(0));

        let mut simulation = SoftwareSystemSimulation::new(&mut system_spec);
        for _ in 0..5 {
            simulation.simulate_system_one_cycle(
                &mut system_spec,
                &mut SystemSimulationCallbacks::default(),
            );
        }
        // node 1 operates on one frames per cycle (in and out); because they frequencies are fully
        // mismatched, node 0 operates on 7 frames at a time, and these persist in its buffers for 5
        // cycles at a time
        let c = &simulation.nodes[0].outputs[0];
        assert_eq!(14, c.frames.len());
        assert_eq!(35, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(false, c.frames[1].valid);
        assert_eq!(3, u8::unpack(c.frames[7].data.as_bitslice()));
        assert_eq!(true, c.frames[7].valid);
        let c = &simulation.nodes[1].outputs[0];
        assert_eq!(14, c.frames.len());
        assert_eq!(35, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
        assert_eq!(0, u8::unpack(c.frames[2].data.as_bitslice()));
        assert_eq!(true, c.frames[2].valid);
        assert_eq!(3, u8::unpack(c.frames[7].data.as_bitslice()));
        assert_eq!(true, c.frames[7].valid);
        assert_eq!(0, u8::unpack(c.frames[8].data.as_bitslice()));
        assert_eq!(true, c.frames[8].valid);
    }

    #[test]
    fn test_faster_sub() {
        let mut system_spec = TestSpec::new();
        let svc_a = Service::new("svc_a", simple_action, None, FrequencyFactor(2));
        let svc_b = Service::new("svc_b", simple_action, None, FrequencyFactor(6));
        let na = system_spec.add_node(svc_a);
        let nb = system_spec.add_node(svc_b);
        let l = TestLink::new(0, 0, Latency(0), 8);
        system_spec.link_simplex_framing(na, nb, l.clone(), FramingLead::Src);
        system_spec.link_simplex_framing(nb, na, l.clone(), FramingLead::Dst);
        // system_spec.link_duplex(&svc_a, 0, 0, &svc_b, 0, 0, 8, 8, Latency(0));
        let mut simulation = SoftwareSystemSimulation::new(&mut system_spec);
        for _ in 0..5 {
            simulation.simulate_system_one_cycle(
                &mut system_spec,
                &mut SystemSimulationCallbacks::default(),
            );
        }
        // node 0 operates on one frames per cycle (in and out); node 1 also operates on individual
        // frames, but because it runs faster, frames from 0 persist in its buffers for 3 cycles at
        // a time
        let c = &simulation.nodes[0].outputs[0];
        assert_eq!(2, c.frames.len());
        assert_eq!(5, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(3, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
        let c = &simulation.nodes[1].outputs[0];
        assert_eq!(2, c.frames.len());
        assert_eq!(5, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(3, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
    }

    #[test]
    fn test_faster_sub_latency() {
        let mut system_spec = TestSpec::new();
        let svc_a = Service::new("svc_a", simple_action, None, FrequencyFactor(2));
        let svc_b = Service::new("svc_b", simple_action, None, FrequencyFactor(6));
        let na = system_spec.add_node(svc_a);
        let nb = system_spec.add_node(svc_b);
        let l = TestLink::new(0, 0, Latency(2), 8);
        system_spec.link_simplex_framing(na, nb, l.clone(), FramingLead::Src);
        system_spec.link_simplex_framing(nb, na, l.clone(), FramingLead::Dst);
        // system_spec.link_duplex(&svc_a, 0, 0, &svc_b, 0, 0, 8, 8, Latency(2));
        let mut simulation = SoftwareSystemSimulation::new(&mut system_spec);
        for _ in 0..5 {
            simulation.simulate_system_one_cycle(
                &mut system_spec,
                &mut SystemSimulationCallbacks::default(),
            );
        }
        // node 0 operates on one frames per cycle (in and out); node 1 also operates on individual
        // frames, but because it runs faster, frames from 0 persist in its buffers for 3 cycles at
        // a time;  because there is a latency of 2 cycles between them, the counts just got started
        // after 5 root cycles
        let c = &simulation.nodes[0].outputs[0];
        assert_eq!(4, c.frames.len());
        assert_eq!(5, c.src_frames_written);
        assert_eq!(1, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
        let c = &simulation.nodes[1].outputs[0];
        assert_eq!(4, c.frames.len());
        assert_eq!(5, c.src_frames_written);
        assert_eq!(1, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
    }

    #[test]
    fn test_faster_sub_primes() {
        let mut system_spec = TestSpec::new();
        let svc_a = Service::new("svc_a", simple_action, None, FrequencyFactor(5));
        let svc_b = Service::new("svc_b", simple_action, None, FrequencyFactor(7));
        let na = system_spec.add_node(svc_a);
        let nb = system_spec.add_node(svc_b);
        let l = TestLink::new(0, 0, Latency(0), 8);
        system_spec.link_simplex_framing(na, nb, l.clone(), FramingLead::Src);
        system_spec.link_simplex_framing(nb, na, l.clone(), FramingLead::Dst);
        // system_spec.link_duplex(&svc_a, 0, 0, &svc_b, 0, 0, 8, 8, Latency(0));
        let mut simulation = SoftwareSystemSimulation::new(&mut system_spec);
        for _ in 0..5 {
            simulation.simulate_system_one_cycle(
                &mut system_spec,
                &mut SystemSimulationCallbacks::default(),
            );
        }
        // node 0 operates on one frames per cycle (in and out); because they frequencies are fully
        // mismatched, node 1 operates on 5 frames at a time, and these persist in its buffers for 7
        // cycles at a time
        let c = &simulation.nodes[0].outputs[0];
        assert_eq!(10, c.frames.len());
        assert_eq!(25, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(true, c.frames[1].valid);
        assert_eq!(3, u8::unpack(c.frames[5].data.as_bitslice()));
        assert_eq!(true, c.frames[5].valid);
        let c = &simulation.nodes[1].outputs[0];
        assert_eq!(10, c.frames.len());
        assert_eq!(25, c.src_frames_written);
        assert_eq!(4, u8::unpack(c.frames[0].data.as_bitslice()));
        assert_eq!(true, c.frames[0].valid);
        assert_eq!(0, u8::unpack(c.frames[1].data.as_bitslice()));
        assert_eq!(false, c.frames[1].valid);
        assert_eq!(0, u8::unpack(c.frames[2].data.as_bitslice()));
        assert_eq!(false, c.frames[2].valid);
        assert_eq!(3, u8::unpack(c.frames[5].data.as_bitslice()));
        assert_eq!(true, c.frames[5].valid);
        assert_eq!(0, u8::unpack(c.frames[6].data.as_bitslice()));
        assert_eq!(false, c.frames[6].valid);
    }

    #[test]
    fn test_link_buffer_write() {
        let mut link_buffer = LinkBuffer::new(10, 32, Latency(0));
        for i in 0..link_buffer.buffer.len() {
            link_buffer.buffer[i].data = u32::pack(&(i as u32)).into_boxed_bitslice();
            link_buffer.buffer[i].valid = true;
        }
        assert_eq!(link_buffer.write_idx, 0);
        assert_eq!(link_buffer.read_idx, 0);
        assert_eq!(link_buffer.occupancy, 0);
        {
            let frames = link_buffer.write_frames(3);
            assert_eq!(u32::unpack(frames[0].data.as_bitslice()), 0);
            assert_eq!(u32::unpack(frames[1].data.as_bitslice()), 1);
            assert_eq!(u32::unpack(frames[2].data.as_bitslice()), 2);
        }
        assert_eq!(link_buffer.occupancy, 3);
        assert_eq!(link_buffer.write_idx, 3);
        assert_eq!(link_buffer.read_idx, 0);
        // Decrement the occupancy so we don't panic on the wrap.
        link_buffer.occupancy -= 1;
        {
            let frames = link_buffer.write_frames(8);
            assert_eq!(u32::unpack(frames[0].data.as_bitslice()), 3);
            assert_eq!(u32::unpack(frames[1].data.as_bitslice()), 4);
            assert_eq!(u32::unpack(frames[2].data.as_bitslice()), 5);
            assert_eq!(u32::unpack(frames[3].data.as_bitslice()), 6);
            assert_eq!(u32::unpack(frames[4].data.as_bitslice()), 7);
            assert_eq!(u32::unpack(frames[5].data.as_bitslice()), 8);
            assert_eq!(u32::unpack(frames[6].data.as_bitslice()), 9);
            assert_eq!(u32::unpack(frames[7].data.as_bitslice()), 0);
        }
        assert_eq!(link_buffer.write_idx, 1);
        assert_eq!(link_buffer.occupancy, 10);
        assert_eq!(link_buffer.read_idx, 0);
    }

    #[test]
    #[should_panic]
    fn test_link_buffer_write_full_panics() {
        let mut link_buffer = LinkBuffer::new(10, 32, Latency(0));
        link_buffer.occupancy = 10;
        link_buffer.write_frames(1);
    }

    #[test]
    fn test_link_buffer_read() {
        let mut link_buffer = LinkBuffer::new(10, 32, Latency(0));
        for i in 0..link_buffer.buffer.len() {
            link_buffer.buffer[i].data = u32::pack(&(i as u32)).into_boxed_bitslice();
            link_buffer.buffer[i].valid = true;
        }
        // Assume full so we can read.
        link_buffer.occupancy = 10;
        assert_eq!(link_buffer.write_idx, 0);
        assert_eq!(link_buffer.read_idx, 0);
        {
            let frames = link_buffer.read_frames(9);
            assert_eq!(u32::unpack(frames[0].data.as_bitslice()), 0);
            assert_eq!(u32::unpack(frames[1].data.as_bitslice()), 1);
            assert_eq!(u32::unpack(frames[2].data.as_bitslice()), 2);
            assert_eq!(u32::unpack(frames[3].data.as_bitslice()), 3);
            assert_eq!(u32::unpack(frames[4].data.as_bitslice()), 4);
            assert_eq!(u32::unpack(frames[5].data.as_bitslice()), 5);
            assert_eq!(u32::unpack(frames[6].data.as_bitslice()), 6);
            assert_eq!(u32::unpack(frames[7].data.as_bitslice()), 7);
            assert_eq!(u32::unpack(frames[8].data.as_bitslice()), 8);
        }
        assert_eq!(link_buffer.write_idx, 0);
        assert_eq!(link_buffer.read_idx, 9);
        assert_eq!(link_buffer.occupancy, 1);
        // Assume some occupancy so we can wrap.
        link_buffer.occupancy += 4;
        {
            let frames = link_buffer.read_frames(3);
            assert_eq!(u32::unpack(frames[0].data.as_bitslice()), 9);
            assert_eq!(u32::unpack(frames[1].data.as_bitslice()), 0);
            assert_eq!(u32::unpack(frames[2].data.as_bitslice()), 1);
        }
        assert_eq!(link_buffer.write_idx, 0);
        assert_eq!(link_buffer.read_idx, 2);
    }

    #[test]
    #[should_panic]
    fn test_link_buffer_read_empty_panics() {
        let mut link_buffer = LinkBuffer::new(10, 32, Latency(0));
        assert_eq!(link_buffer.occupancy, 0);
        link_buffer.read_frames(1);
    }
}
