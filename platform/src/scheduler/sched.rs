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

use itertools::Itertools;

use crate::app::CommsHandle;
use crate::app::ServiceHandle;
use crate::calendar::calendar_depth;
use crate::calendar::Calendar;
use crate::calendar::CalendarEntry;
use crate::calendar::CrossbarCalendar;
use crate::calendar::CrossbarCalendarEntry;
use crate::calendar::NodeCalendar;
use crate::calendar::NodeCalendarEntry;
use crate::scheduler::alloc::compute_batch_size;
use crate::scheduler::alloc::SystemAllocation;
use crate::scheduler::reservation::ReservationTable;
use crate::AllocationPolicy;
use crate::Buffering;
use crate::BUFFERING_DOUBLE;
use crate::{Application, Error, HardwareSpec, NodeSpec};
use petgraph::prelude::*;
use std::collections::HashMap;

use super::{get_switch_calendars_1x1_network, node_frequency_ratios};

/// Scheduler representation
///
/// A set of actions and their starting metacycle for each compute node
/// A pair of calendars for each link.
/// A set of crossbar calendars for each switch.
#[derive(Clone, Debug)]
pub struct Schedule<const BUFFERING: Buffering> {
    pub node_schedules: HashMap<NodeIndex, [NodeCalendar; BUFFERING]>,
    // For link (src -> dst) with edge-index (key) map to values: (src-calendar, dst-calendar)
    pub link_schedules: HashMap<EdgeIndex, [(Calendar, Calendar); BUFFERING]>,
    pub switch_schedules: HashMap<NodeIndex, [CrossbarCalendar; BUFFERING]>,
}

impl Schedule<{ BUFFERING_DOUBLE }> {
    pub fn new() -> Self {
        Self {
            node_schedules: HashMap::new(),
            link_schedules: HashMap::new(),
            switch_schedules: HashMap::new(),
        }
    }

    /// generate the (tx, rx) calendars for a link
    fn generate_link_calendar_1x1(
        &mut self,
        sys_spec: &HardwareSpec,
        app_spec: &Application,
        system_allocation: &SystemAllocation,
        app_link: EdgeIndex,
    ) -> Result<(), Error> {
        let sys_path = system_allocation.links[&CommsHandle::new(app_spec.id(), app_link)]
            .as_ref()
            .unwrap();
        let app_message_length = app_spec.get_link(app_link).frame_size();

        let physical_frame_size = sys_spec.get_link(sys_path.source()).frame_size();
        let batching = compute_batch_size(sys_spec, sys_path);
        log::trace!(
            "generating calendar: link {} app frame size: {} hw frame size: {}",
            app_link.index(),
            app_message_length,
            physical_frame_size
        );
        // 1x1 mapping paths can only have a single destination.
        assert_eq!(sys_path.destinations().len(), 1);
        let path_last_hop = sys_path.destinations()[0];
        let (src_node_id, _) = sys_spec.get_link_endpoints(sys_path.source());
        let (_, dst_node_id) = sys_spec.get_link_endpoints(path_last_hop);
        let [src_cpm, _] = sys_spec
            .get_node(src_node_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .cycles_per_metacycle();
        let [dst_cpm, _] = sys_spec
            .get_node(dst_node_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .cycles_per_metacycle();
        let n_frames = app_message_length / physical_frame_size
            + usize::from(app_message_length % physical_frame_size != 0);
        // src node communicates batch-frames every B * f_tx / f_link cycles
        // let src_cycles_per_batch = (batch_size * src_freq) / link_freq;
        let src_steps = (src_cpm / batching.src_cycles
            + usize::from(src_cpm % batching.src_cycles != 0))
            * batching.batch_size;
        let dst_cycles_per_batch = batching.dst_cycles[&path_last_hop];
        assert_eq!(batching.dst_cycles.len(), 1);
        let dst_steps = (dst_cpm / dst_cycles_per_batch
            + usize::from(dst_cpm % dst_cycles_per_batch != 0))
            * batching.batch_size;
        log::trace!(
            "path\n{} batch size: {}, tx cycles-per-batch: {}, rx cycles-per-batch: {}, tx-cpm: {}, rx-cpm: {}, tx-steps: {}, rx-steps: {}",
            sys_path.all_links().iter().map(|link_id| {
                let (src, dst) = sys_spec.get_link_endpoints(*link_id);
                format!("{} ---{:?}---> {}", sys_spec.get_node(src).borrow().name(), *link_id,  sys_spec.get_node(dst).borrow().name())
            }).join(",\n"), batching.batch_size, batching.src_cycles, dst_cycles_per_batch, src_cpm, dst_cpm, src_steps, dst_steps);
        let path_latency = sys_path.path_latencies(sys_spec);
        let latency = path_latency[&path_last_hop];
        let src_tx_clock = sys_spec
            .get_node(src_node_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles() as i64;
        let dst_clock = sys_spec
            .get_node(dst_node_id)
            .borrow()
            .into_provisioned_node()
            .unwrap()
            .starting_cycles();
        let dst_rx_clock = src_tx_clock + latency;
        assert!(dst_rx_clock as usize >= dst_clock);
        let dst_delay_from_start_of_metacycle = dst_rx_clock as usize - dst_clock;
        for sys_link_id in sys_path.all_links() {
            let mut tx_calendar = Calendar::new();
            let mut rx_calendar = Calendar::new();
            let (link_src_id, link_dst_id) = sys_spec.get_link_endpoints(sys_link_id);

            if link_src_id == src_node_id {
                let src_outboxes = sys_spec
                    .get_node(link_src_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .get_mailbox()
                    .expect(
                        format!(
                            "HW node {:?} is required to have an associated mailbox post allocation.",
                            src_node_id
                        )
                        .as_str(),
                    ).get_src_port_outboxes(sys_spec.get_link(sys_link_id).src_port().into());
                assert_eq!(src_outboxes.len(), 1); // 1x1 mapping assumption
                tx_calendar.push(CalendarEntry::new(
                    src_outboxes[0]
                        .mapped_endpoint
                        .as_ref()
                        .unwrap()
                        .base_address
                        .map(|a| a as u32),
                    n_frames,
                ));
                if src_steps > n_frames {
                    tx_calendar.push(CalendarEntry::new(None, src_steps - n_frames));
                }
            } else {
                let [link_src_cpm, _] = sys_spec
                    .get_node(link_src_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .cycles_per_metacycle();
                tx_calendar = vec![CalendarEntry::new(Some(0), 1); link_src_cpm];
            }
            if link_dst_id == dst_node_id {
                if dst_delay_from_start_of_metacycle > 0 {
                    rx_calendar.push(CalendarEntry {
                        base_address: None,
                        frame_count: dst_delay_from_start_of_metacycle as u32,
                    });
                }
                let dst_inboxes = sys_spec
                    .get_node(dst_node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .get_mailbox()
                    .expect(
                        format!(
                            "HW node {:?} is required to have an associated mailbox post allocation.",
                            dst_node_id
                        ).as_str()
                    ).get_dst_port_inboxes(sys_spec.get_link(sys_link_id).dst_port().into());
                assert_eq!(dst_inboxes.len(), 1); // 1x1 mapping assumption
                rx_calendar.push(CalendarEntry::new(
                    dst_inboxes[0]
                        .mapped_endpoint
                        .as_ref()
                        .unwrap()
                        .base_address
                        .map(|a| a as u32),
                    n_frames,
                ));
                if dst_steps > n_frames + dst_delay_from_start_of_metacycle {
                    rx_calendar.push(CalendarEntry::new(
                        None,
                        dst_steps - n_frames - dst_delay_from_start_of_metacycle,
                    ));
                }
            } else {
                let [link_dst_cpm, _] = sys_spec
                    .get_node(link_dst_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .cycles_per_metacycle();
                rx_calendar = vec![CalendarEntry::new(Some(0), 1); link_dst_cpm];
            }
            log::trace!(
                "generated calendars: link {:?},\ntx {:?}\nrx: {:?}",
                sys_link_id,
                tx_calendar,
                rx_calendar
            );
            let tx_depth = calendar_depth(&tx_calendar);
            let rx_depth = calendar_depth(&rx_calendar);
            self.link_schedules.insert(
                sys_link_id,
                [
                    (
                        vec![CalendarEntry::new(None, tx_depth)],
                        vec![CalendarEntry::new(None, rx_depth)],
                    ),
                    (tx_calendar, rx_calendar),
                ],
            );
        }

        Ok(())
    }

    pub(super) fn generate_calendars_1x1(
        &mut self,
        sys_spec: &HardwareSpec,
        app_spec: &Application,
        alloc: &SystemAllocation,
        policy: &AllocationPolicy,
        system_wide_period: usize,
    ) -> Result<(), Error> {
        if let AllocationPolicy::OneToOneNetwork(_) = policy {
            self.switch_schedules =
                get_switch_calendars_1x1_network(app_spec, sys_spec, alloc, system_wide_period)
                    .drain()
                    .map(|(switch_id, calendar)| {
                        let cal_depth = calendar_depth(&calendar);
                        (
                            switch_id,
                            [vec![CrossbarCalendarEntry::new(None, cal_depth)], calendar],
                        )
                    })
                    .collect::<HashMap<_, _>>();
        }
        let freq_ratios = node_frequency_ratios(sys_spec);
        self.node_schedules = sys_spec
            .compute_nodes()
            .iter()
            .map(|node_id| {
                let freq_ratio = freq_ratios[&node_id];
                let node_cpm = system_wide_period * freq_ratio;
                let (app_node_id, _) = alloc
                    .nodes
                    .iter()
                    .find(|(_, alloc_node_id)| **alloc_node_id == *node_id)
                    .unwrap();
                assert!(
                    alloc.compute_cycles[&ServiceHandle::new(app_spec.id(), *node_id)] <= node_cpm
                ); // guaranteed by the system_wide_period
                let mut calendar = vec![];
                calendar.push(NodeCalendarEntry::new(
                    Some(ServiceHandle::new(app_spec.id(), app_node_id.service_id)),
                    alloc.compute_cycles[&ServiceHandle::new(app_spec.id(), *node_id)],
                ));
                if node_cpm > alloc.compute_cycles[&ServiceHandle::new(app_spec.id(), *node_id)] {
                    calendar.push(NodeCalendarEntry::new(
                        None,
                        node_cpm
                            - alloc.compute_cycles[&ServiceHandle::new(app_spec.id(), *node_id)],
                    ));
                }
                let cal_depth = calendar_depth(&calendar);
                (
                    *node_id,
                    [calendar, vec![NodeCalendarEntry::new(None, cal_depth)]],
                )
            })
            .collect::<HashMap<_, _>>();
        for app_link in alloc.links.keys() {
            self.generate_link_calendar_1x1(sys_spec, app_spec, &alloc, app_link.edge_id)?;
        }
        Ok(())
    }

    /// Generates the calendars from a reservation table schedule.
    pub(super) fn generate_calendars(
        &mut self,
        rsv: &[ReservationTable; BUFFERING_DOUBLE],
        sys_spec: &HardwareSpec,
    ) -> Result<(), Error> {
        for node_id in sys_spec.iter_nodes() {
            if sys_spec
                .get_node(node_id)
                .borrow()
                .into_provisioned_switch_node()
                .is_some()
            {
                self.switch_schedules.insert(
                    node_id,
                    [0, 1].map(|i| {
                        rsv[i]
                            .switch_calendar(&node_id, sys_spec)
                            .expect("Failed to generate switch calendar.")
                    }),
                );
            } else {
                self.node_schedules.insert(
                    node_id,
                    [0, 1].map(|i| {
                        rsv[i]
                            .node_calendar(&node_id, sys_spec)
                            .expect("Failed to generate node calendar.")
                    }),
                );
            }
            for edge_ref in sys_spec.get_output_links(node_id) {
                self.link_schedules.insert(
                    edge_ref.id(),
                    [0, 1].map(|i| {
                        rsv[i]
                            .link_calendar(&edge_ref.id(), sys_spec)
                            .expect("Failed to generate scatter/gather calendars.")
                    }),
                );
            }
        }
        let node_frequencies = sys_spec
            .iter_nodes()
            .map(|node_id| {
                sys_spec
                    .get_node(node_id)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .frequency()
                    .value
            })
            .collect::<Vec<_>>();
        let link_frequencies = sys_spec
            .iter_links()
            .map(|link_id| {
                sys_spec
                    .get_link(link_id)
                    .into_provisioned_link()
                    .unwrap()
                    .frequency()
                    .value
            })
            .collect::<Vec<_>>();
        // The system-period is an integer multiple of every resources's period, then
        // SystemPeriod = 1 / GCD({ frequency(node_k) })
        let inverse_system_period = node_frequencies
            .iter()
            .chain(link_frequencies.iter())
            .copied()
            .reduce(|accum, x| num::integer::gcd(accum, x))
            .unwrap();
        // PeriodMultiple = SystemPeriod / NodePeriod
        //                = (1 / InverseSystemPeriod) / (1 / NodeFrequency)
        //                = NodeFrequency / InverseSystemPeriod
        let node_period_multiples = node_frequencies
            .iter()
            .map(|f| f / inverse_system_period)
            .collect::<Vec<_>>();
        let link_period_multiples = link_frequencies
            .iter()
            .map(|f| f / inverse_system_period)
            .collect::<Vec<_>>();
        // Number of cycles to exhaust each node's calendar (at the node's frequency)
        let node_calendar_depths = sys_spec
            .iter_nodes()
            .map(|node_id| {
                if sys_spec
                    .get_node(node_id)
                    .borrow()
                    .into_provisioned_switch_node()
                    .is_some()
                {
                    self.switch_schedules[&node_id]
                        .clone()
                        .map(|calendar| calendar_depth(&calendar))
                } else {
                    self.node_schedules[&node_id]
                        .clone()
                        .map(|calendar| calendar_depth(&calendar))
                }
            })
            .collect::<Vec<_>>();
        // Number of cycles to exhaust each link's calendar (at the link's frequency)
        let link_calendar_depths = sys_spec
            .iter_links()
            .map(|link_id| {
                self.link_schedules[&link_id]
                    .clone()
                    .map(|cals| (calendar_depth(&cals.0), calendar_depth(&cals.1)))
            })
            .collect::<Vec<_>>();
        let max_node_sys_periods = node_calendar_depths
            .iter()
            .zip(node_period_multiples.iter())
            .map(|(cycles, cycles_per_sys_period)| {
                cycles.map(|cycles| {
                    cycles / cycles_per_sys_period
                        + usize::from(cycles % cycles_per_sys_period != 0)
                })
            })
            .max()
            .unwrap_or([0; BUFFERING_DOUBLE]);
        let max_link_sys_periods = link_calendar_depths
            .iter()
            .zip(link_period_multiples.iter())
            .map(|(endpoint_cals, cycles_per_sys_period)| {
                endpoint_cals.map(|(src_cycles, dst_cycles)| {
                    let max_cycles = src_cycles.max(dst_cycles);
                    max_cycles / cycles_per_sys_period
                        + usize::from(max_cycles % cycles_per_sys_period != 0)
                })
            })
            .max()
            .unwrap_or([0; BUFFERING_DOUBLE]);
        // We can't have empty metacycles (size 0), to prevent that we force a minimum value of 1 here.
        let sys_periods_per_metacycle = [
            std::cmp::max(
                1,
                std::cmp::max(max_node_sys_periods[0], max_link_sys_periods[0]),
            ),
            std::cmp::max(
                1,
                std::cmp::max(max_node_sys_periods[1], max_link_sys_periods[1]),
            ),
        ];

        // Pad the node calendars
        for ((node_id, cycles_per_sys_period), depth) in sys_spec
            .iter_nodes()
            .zip(node_period_multiples.iter())
            .zip(node_calendar_depths.iter())
        {
            let node_cpm = sys_periods_per_metacycle.map(|x| x * cycles_per_sys_period);
            sys_spec
                .get_node(node_id)
                .borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_cycles_per_metacycle(node_cpm);
            assert!(node_cpm[0] >= depth[0] && node_cpm[1] >= depth[1]);
            if sys_spec
                .get_node(node_id)
                .borrow()
                .into_provisioned_switch_node()
                .is_some()
            {
                for i in 0..BUFFERING_DOUBLE {
                    if node_cpm[i] > depth[i] {
                        self.switch_schedules.get_mut(&node_id).unwrap()[i]
                            .push(CrossbarCalendarEntry::new(None, node_cpm[i] - depth[i]))
                    }
                }
            } else {
                for i in 0..BUFFERING_DOUBLE {
                    if node_cpm[i] > depth[i] {
                        self.node_schedules.get_mut(&node_id).unwrap()[i]
                            .push(NodeCalendarEntry::new(None, node_cpm[i] - depth[i]))
                    }
                }
            }
        }
        // Pad the link calendars
        for ((link_id, link_depths), cycles_per_sys_period) in sys_spec
            .iter_links()
            .zip(link_calendar_depths)
            .zip(link_period_multiples.iter())
        {
            for i in 0..BUFFERING_DOUBLE {
                let (src_depth, dst_depth) = link_depths[i];
                let link_cpm = sys_periods_per_metacycle[i] * cycles_per_sys_period;
                assert!(link_cpm >= src_depth);
                assert!(link_cpm >= dst_depth);
                let (src_calendar, dst_calendar) = self
                    .link_schedules
                    .get_mut(&link_id)
                    .unwrap()
                    .get_mut(i)
                    .unwrap();
                if link_cpm > src_depth {
                    src_calendar.push(CalendarEntry {
                        base_address: None,
                        frame_count: (link_cpm - src_depth) as u32,
                    });
                }
                if link_cpm > dst_depth {
                    dst_calendar.push(CalendarEntry {
                        base_address: None,
                        frame_count: (link_cpm - dst_depth) as u32,
                    });
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hw::compute::ComputeNode;
    use crate::scheduler::{AllocateTrait, AllocationPolicy, MappingConfiguration1x1};
    use crate::specs::SystemContext;
    use crate::*;

    // action to use for the app_spec
    fn no_action(
        _state: LoopbackRef,
        _in: &[InputFrameRef],
        _out: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
    }

    #[test]
    fn test_link_calendars() {
        const N_LINKS: usize = 5;
        const LATENCY: usize = 1;
        const HW_FRAME_SIZE: usize = 32;
        // The largest 2*N_LINKS - 1 HW frames, requiring at least that many cycles per metacycle.
        const CYCLES_PER_METACYCLE: usize = LATENCY + 2 * N_LINKS - 1;

        // create the topologies: a 2 node system connected by 2*N_LINKS bidir links.
        //
        //   Each edge is annotated by the size of the message in HW frames, since N_LINKS=5,
        //   the largest message size is 2*N_LINKS - 1 = 9 frames.
        //
        //   Node 0 and 1 both operate at frequency 1 (no batching); therefore the number of
        //   cycles required to transmit all frames from node 1 to node 0 is 9 cycles plus an
        //   additional cycle to cover the latency of the link.
        //
        //   +-----------+              +-----------+
        //   |           |-------1----->|           |
        //   |           |<------5------|           |
        //   |           |              |           |
        //   |           |-------2----->|           |
        //   |           |<------6------|           |
        //   |           |              |           |
        //   |           |-------3----->|           |
        //   |  node 0   |<------7------|   node 1  |
        //   |           |              |           |
        //   |           |-------4----->|           |
        //   |           |<------8------|           |
        //   |           |              |           |
        //   |           |-------5----->|           |
        //   |           |<------9------|           |
        //   |           |              |           |
        //   +-----------+              +-----------+

        // We are not calling generate_physical_system_1x1 because that will
        // create hardware links that have the same configuration as the app
        // links. Here we actually want to see the mapping of application
        // messages to a fixed hardware frame size.
        let mut node_config = vec![NodeConfiguration::default(), NodeConfiguration::default()];
        for n in 0..=1 {
            node_config[n].frequency = 1;
            node_config[n].cycles_per_metacycle = CYCLES_PER_METACYCLE;
        }

        // create the application topology
        let mut app_spec = Application::new();
        let app_node0 =
            app_spec.add_node(Service::new("node0", no_action, None, FrequencyFactor(1)));
        let app_node1 =
            app_spec.add_node(Service::new("node1", no_action, None, FrequencyFactor(1)));

        let link_config = LinkConfiguration {
            frame_size: HW_FRAME_SIZE,
            ..Default::default()
        };
        for l in 0..N_LINKS {
            // n0 outgoing links with frame sizes HW_FRAME_SIZE:(N_LINKS * HW_FRAME_SIZE)
            node_config[1].add_link(
                &link_config,
                Port::new(
                    l,
                    &PortProperties {
                        direction: Direction::Incoming,
                        frame_size: HW_FRAME_SIZE.into(),
                        ..Default::default()
                    },
                ),
            );
            node_config[0].add_link(
                &link_config,
                Port::new(
                    l,
                    &PortProperties {
                        direction: Direction::Outgoing,
                        frame_size: HW_FRAME_SIZE.into(),
                        ..Default::default()
                    },
                ),
            );
            let conn = Connection::new_for_testing(l, l, (l + 1) * link_config.frame_size);
            app_spec.link_simplex_framing(app_node0, app_node1, conn, FramingLead::Src);

            // n1 outgoing links with frame sizes (N_LINKS*HW_FRAME_SIZE):(2*N_LINKS*HW_FRAME_SIZE)
            node_config[0].add_link(
                &link_config,
                Port::new(
                    l,
                    &PortProperties {
                        direction: Direction::Incoming,
                        frame_size: HW_FRAME_SIZE.into(),
                        ..Default::default()
                    },
                ),
            );
            node_config[1].add_link(
                &link_config,
                Port::new(
                    l,
                    &PortProperties {
                        direction: Direction::Outgoing,
                        frame_size: HW_FRAME_SIZE.into(),
                        ..Default::default()
                    },
                ),
            );
            let conn = Connection::new_for_testing(l, l, (l + N_LINKS) * link_config.frame_size);
            app_spec.link_simplex_framing(app_node1, app_node0, conn, FramingLead::Src);
        }

        // create the hardware topology.
        let mut system_spec = HardwareSpec::new();
        let node0 = system_spec.add_node(Node::ComputeNode(ComputeNode::from_config(
            "node0",
            &node_config[0],
        )));
        let node1 = system_spec.add_node(Node::ComputeNode(ComputeNode::from_config(
            "node1",
            &node_config[1],
        )));
        node_config[0]
            .output_links
            .iter()
            .enumerate()
            .for_each(|(l, link_config)| {
                system_spec.link_simplex(
                    node0,
                    node1,
                    Link::from_config(
                        l,
                        l,
                        LinkConfiguration {
                            latency: LATENCY,
                            ..*link_config
                        },
                    ),
                );
            });
        node_config[1]
            .output_links
            .iter()
            .enumerate()
            .for_each(|(l, link_config)| {
                system_spec.link_simplex(
                    node1,
                    node0,
                    Link::from_config(
                        l,
                        l,
                        LinkConfiguration {
                            latency: LATENCY,
                            ..*link_config
                        },
                    ),
                );
            });

        let allocation_policy = AllocationPolicy::OneToOne(MappingConfiguration1x1::default());
        // create the allocations: the one_to_one default allocation should
        // work for this case, since we effectively created a 1x1
        // mapping and all the hardware links are identical.
        let allocation = system_spec
            .allocate(&[&app_spec], &allocation_policy)
            .expect("Failed to allocate");

        let mut scheduler = Schedule::new();

        // validate the calendars
        for app_link in app_spec.get_output_links(app_node0) {
            let path = allocation.links[&CommsHandle::new(app_spec.id(), app_link.id())]
                .as_ref()
                .unwrap();
            assert_eq!(path.all_links().len(), 1);
            let sys_link_id = path.source();
            scheduler
                .generate_link_calendar_1x1(&system_spec, &app_spec, &allocation, app_link.id())
                .expect(&format!(
                    "failed to generate calendar for {:?}:{:?}",
                    app_node0.index(),
                    app_link.id()
                ));
            if let Some([_, (tx_cal, rx_cal)]) = scheduler.link_schedules.get(&sys_link_id) {
                println!(
                    "app_link: {:?} - tx cal {:#?}, rx cal {:#?}",
                    sys_link_id, tx_cal, rx_cal
                );
                // compute the frame sizes and verify that the calendars have them
                let src_port: usize = system_spec.get_link(sys_link_id).src_port().into();
                let n_frames = (src_port + 1) as u32;
                println!("tx_cal: {:#?}", tx_cal);
                assert_eq!(
                    tx_cal.len() as u32,
                    if n_frames < CYCLES_PER_METACYCLE as u32 {
                        2
                    } else {
                        1
                    }
                );
                println!("rx_cal: {:#?}", rx_cal);
                assert_eq!(
                    rx_cal.len() as u32,
                    if n_frames < CYCLES_PER_METACYCLE as u32 {
                        u32::from(LATENCY > 0) + 2
                    } else {
                        u32::from(LATENCY > 0) + 1
                    }
                );
                assert_eq!(tx_cal[0].frame_count, n_frames);
                assert_eq!(tx_cal[0].base_address.unwrap(), 0);
                if n_frames < CYCLES_PER_METACYCLE as u32 {
                    assert!(tx_cal[1].base_address.is_none());
                }
                // The RX side of a link has an initial calendar entry to cover the
                // latency of the link.
                assert_eq!(rx_cal[0].frame_count, LATENCY as u32);
                assert!(rx_cal[0].base_address.is_none());
                // The data portion.
                assert_eq!(rx_cal[1].frame_count, n_frames);
                assert_eq!(rx_cal[1].base_address.unwrap(), 0);
                if n_frames < CYCLES_PER_METACYCLE as u32 {
                    // Idle cycles to fill the metacycle.
                    assert!(rx_cal[2].base_address.is_none());
                    assert_eq!(
                        rx_cal[2].frame_count as usize,
                        CYCLES_PER_METACYCLE - (n_frames as usize) - LATENCY
                    );
                }
            } else {
                panic!(
                    "Can not find calendar for app link {:?} mapped to sys link {:?}",
                    app_link.id(),
                    sys_link_id
                );
            }
        }
    }
}
