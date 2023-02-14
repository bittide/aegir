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

//! Test that we can induce node/switch crashes.

use bits::*;
use bits_derive::Bits;
use itertools::Itertools;
use platform::specs::ApplicationNode;
use platform::specs::LinkStatus;
use platform::Application;
use platform::FailureProperties;
use platform::NodeIndex;
use platform::NodeSpec;
use platform::SystemContext;
use platform::SystemSimulationCallbacks;
use std::collections::HashMap;

const STARTING_CYCLE: u32 = 1;
const NUM_NODES: usize = 4;
const NUM_LINKS: usize = NUM_NODES - 1;

#[derive(Bits, Clone, Copy, Debug, PartialEq)]
pub struct State {
    id: u32,
    metacycle: u32,
    // Last local cycle in which we received a message which was Some from
    // each node. Indexed by node ID.
    last_cycle_message_some: [u32; NUM_NODES],
    // Last local cycle in which an input link from a given node was active.
    // Note the ith input isn't from the ith node, but we map it back so this
    // is correctly indexed by node ID.
    last_cycle_input_active: [u32; NUM_NODES],
    // Last local cycle in which an output link was active. Indexed by node ID.
    // Note the ith output isn't from the ith node, but we map it back so this
    // is correctly indexed by node ID.
    last_cycle_output_active: [u32; NUM_NODES],
}

impl State {
    pub fn new(id: u32) -> Self {
        assert!(id < NUM_NODES as u32);
        Self {
            metacycle: STARTING_CYCLE,
            id: id,
            last_cycle_message_some: [0u32; NUM_NODES],
            last_cycle_input_active: [0u32; NUM_NODES],
            last_cycle_output_active: [0u32; NUM_NODES],
        }
    }
}

fn summarize_link_status(sys: &dyn SystemContext) -> String {
    format!(
        "(inputs=[{}], outputs=[{}])",
        sys.input_links().iter().map(|i| i.status).format(", "),
        sys.output_links().iter().map(|i| i.status).format(", "),
    )
}

waves::action_fn! {
    increment_counters
    (state: State)
    (input: [Option<u32>; NUM_LINKS]) -> (output: [u32; NUM_LINKS]) {
        log::info!(
            "increment_counters cycle={} id={} input={:?} links={} state={:?}",
            state.metacycle, state.id, input, summarize_link_status(sys), state,
        );

        let input_links = sys.input_links();
        assert_eq!(input_links.len(), NUM_LINKS);
        let output_links = sys.output_links();
        assert_eq!(output_links.len(), NUM_LINKS);

        for i in 0..NUM_LINKS {
            // Record the last cycle in which the *input* from each Node was Some.
            let src = link_dst_input_index_to_src(state.id as usize, i);
            if input[i].is_some() {
                let src_send_cycle = input[i].unwrap();
                assert_eq!(state.metacycle, src_send_cycle+1, "We should be receving last cycle's message");
                state.last_cycle_message_some[src] = state.metacycle;
            }

            // Record the last cycle in which the *input link* from each Node was active.
            if input_links[i].status == LinkStatus::Up {
                state.last_cycle_input_active[src] = state.metacycle as u32;
            }

            // Record the last cycle in which the *output link* to each Node was active.
            if output_links[i].status == LinkStatus::Up {
                let dst = link_src_index_to_dst(state.id as usize, i);
                state.last_cycle_output_active[dst] = state.metacycle as u32;
            }
        }

        output = [state.metacycle; NUM_LINKS];

        state.metacycle += 1;
    }
}

fn link_src_dst_to_input_index(src: usize, dst: usize) -> usize {
    assert_ne!(src, dst, "Can't have self links");
    if src > dst {
        src - 1
    } else {
        src
    }
}

fn link_dst_input_index_to_src(dst: usize, index: usize) -> usize {
    if index < dst {
        index
    } else {
        index + 1
    }
}

fn link_src_index_to_dst(src: usize, index: usize) -> usize {
    if index < src {
        index
    } else {
        index + 1
    }
}

fn build_app() -> Application {
    // Build a topology of NUM_NODES nodes, which send their cycle counter to
    // every other node, recording when the messages start arriving as None,
    // and when the links go down.

    let mut app_spec = Application::new();

    let nodes = (0..NUM_NODES)
        .map(|i| {
            let name = &format!("node_{}", i);
            waves::action!(
                &name in app_spec
                (state: State)
                (input: [Option<u32>; NUM_LINKS]) -> (output: [u32; NUM_LINKS])
                { Bits::pack(&State::new(i as u32)).into_boxed_bitslice() }
                increment_counters
            )
        })
        .collect::<Vec<_>>();

    for src in 0..NUM_NODES {
        let mut out_index = 0;
        for dst in 0..NUM_NODES {
            if dst == src {
                continue;
            }

            // Assert if we have two of (src, dst, index) we can get the third.
            let link_index = link_src_dst_to_input_index(src, dst);
            let predicted_src = link_dst_input_index_to_src(dst, link_index);
            assert_eq!(predicted_src, src);
            let predicted_dst = link_src_index_to_dst(src, out_index);
            assert_eq!(predicted_dst, dst);

            waves::link!(nodes[src] output[out_index] -> nodes[dst] input[link_index] in app_spec);
            out_index += 1;
        }
    }

    app_spec
}

fn retrieve_state(idx: NodeIndex, app_spec: &Application) -> State {
    let node = app_spec.get_node(idx);
    let node_ref = node.borrow();
    let stateful_node = node_ref.into_stateful_node().unwrap();
    let bitbox = stateful_node.persistent_state().unwrap();
    State::unpack(bitbox)
}

pub fn run_simulate_node_crash(
    allocation: platform::AllocationPolicy,
    induced_crashes: HashMap<String, usize>,
    num_cycles: usize,
) -> Vec<State> {
    let app_spec = build_app();
    let system_spec = platform::generate_system_spec(&app_spec, &allocation);
    let res = platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        allocation,
        None,
        num_cycles,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties {
            frame_corruption_rate: 0.0,
            // Note: bake in the seed so behavior is deterministic.
            induced_crashes,
            ..Default::default()
        },
    );
    res.expect("Failed to run bittide");

    let mut states = vec![];
    for i in 0..NUM_NODES {
        let state = retrieve_state(NodeIndex::new(i), &app_spec);
        log::info!("STATE: {:?} ", state);
        states.push(state);
    }

    states
}

#[cfg(test)]
mod tests {
    use super::run_simulate_node_crash;
    use super::State;
    use std::collections::HashMap;

    const FRAME_SIZE: usize = 64;

    #[test]
    fn simulate_compute_node_crash_one_to_one_allocation() {
        let _ = env_logger::try_init();

        // There are two metacycles per complete round; the first to run
        // compute, the second to transmit/receive the results.
        // The first round of compute runs before any data is received from other nodes.
        // We have four nodes, node_{0,1,2,3}.
        // With a one to one allocation, there are no switch nodes.
        // node_1 crashes at the start of metacycle 2 (after 1 compute + 1 tx/rx cycle).
        // node_2 crashes at the start of metacycle 4 (after 2 rounds of compute + tx/rx.
        let states = run_simulate_node_crash(
            platform::AllocationPolicy::OneToOne(platform::MappingConfiguration1x1 {
                frame_size: FRAME_SIZE,
                ..Default::default()
            }),
            HashMap::from([("node_1".to_owned(), 2), ("node_2".to_owned(), 4)]),
            10,
        );
        log::info!("{:?}", states);

        let expected_states = vec![
            State {
                id: 0,
                metacycle: 6,
                last_cycle_message_some: [0, 2, 3, 5],
                last_cycle_input_active: [0, 1, 2, 5],
                last_cycle_output_active: [0, 1, 2, 5],
            },
            State {
                id: 1,
                metacycle: 2, // STARTING_CYCLE (1) + 1 compute round.
                last_cycle_message_some: [0, 0, 0, 0],
                last_cycle_input_active: [1, 0, 1, 1],
                last_cycle_output_active: [1, 0, 1, 1],
            },
            State {
                id: 2,
                metacycle: 3, // STARTING_CYCLE (1) + 2 compute rounds.
                last_cycle_message_some: [2, 2, 0, 2],
                last_cycle_input_active: [2, 1, 0, 2],
                last_cycle_output_active: [2, 1, 0, 2],
            },
            State {
                id: 3,
                metacycle: 6,
                last_cycle_message_some: [5, 2, 3, 0],
                last_cycle_input_active: [5, 1, 2, 0],
                last_cycle_output_active: [5, 1, 2, 0],
            },
        ];
        assert_eq!(expected_states, states);
    }

    #[test]
    fn simulate_compute_node_crash_one_to_one_network_allocation() {
        let _ = env_logger::try_init();

        // We have four nodes, node_{0,1,2,3}.
        // Each node has a switch node_{0,1,2,3}_switch.
        // We crash node_1_switch at the start of metacycle 4.
        // It takes two metacycles to run all nodes compute and comms,
        // as we currently don't overlap comms with compute.
        // As node_1_switch crashes after running comms+compute twice,
        // other nodes should get one round of non-None input from it.
        // Note that the links to/from node_1 will appear as up, as
        // only its *switch* crashed, and every node has their own switch
        // between them and the crashed switch. So app nodes can't observe
        // the switch crashing; they just stop getting messages from node_1.
        let states = run_simulate_node_crash(
            platform::AllocationPolicy::OneToOneNetwork(platform::MappingConfiguration1x1Network {
                frame_size: FRAME_SIZE,
                ..Default::default()
            }),
            HashMap::from([("node_1_switch".to_owned(), 4)]),
            10,
        );
        log::info!("{:?}", states);

        let expected_states = vec![
            State {
                id: 0,
                metacycle: 6,
                last_cycle_message_some: [0, 3, 5, 5],
                last_cycle_input_active: [0, 5, 5, 5],
                last_cycle_output_active: [0, 5, 5, 5],
            },
            State {
                id: 1,
                metacycle: 6,
                last_cycle_message_some: [3, 0, 3, 3],
                last_cycle_input_active: [2, 0, 2, 2],
                last_cycle_output_active: [2, 0, 2, 2],
            },
            State {
                id: 2,
                metacycle: 6,
                last_cycle_message_some: [5, 3, 0, 5],
                last_cycle_input_active: [5, 5, 0, 5],
                last_cycle_output_active: [5, 5, 0, 5],
            },
            State {
                id: 3,
                metacycle: 6,
                last_cycle_message_some: [5, 3, 5, 0],
                last_cycle_input_active: [5, 5, 5, 0],
                last_cycle_output_active: [5, 5, 5, 0],
            },
        ];
        assert_eq!(expected_states, states);
    }
}
