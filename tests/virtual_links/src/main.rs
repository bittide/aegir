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

//! A fully connected graph of service functions is mapped to a fat-tree topology.
use bits::*;
use bits_derive::Bits;
use platform::fat_tree;
use platform::specs::ApplicationNode;
use platform::Application;
use platform::Error;
use platform::FailureProperties;
use platform::HardwareSpec;
use platform::LinkConfiguration;
use platform::NodeConfiguration;
use platform::RandomAllocation;
use platform::SwitchConfiguration;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;
use serde::Serialize;

type MsgType = u32;

#[derive(Clone, Debug, Serialize, Bits)]
struct NodeState {
    counter: u32,
    node_idx: u32,
}

waves::action_fn! {
    node6
    (state: NodeState)
    (input0: Option<MsgType>,
     input1: Option<MsgType>,
     input2: Option<MsgType>,
     input3: Option<MsgType>,
     input4: Option<MsgType>)
    ->
    (output0: MsgType,
     output1: MsgType,
     output2: MsgType,
     output3: MsgType,
     output4: MsgType) {
        let val0 = input0.map(|_| 1).unwrap_or(0);
        let val1 = input1.map(|_| 1).unwrap_or(0);
        let val2 = input2.map(|_| 1).unwrap_or(0);
        let val3 = input3.map(|_| 1).unwrap_or(0);
        let val4 = input4.map(|_| 1).unwrap_or(0);
        output0 = state.node_idx << 16 | 0;
        output1 = state.node_idx << 16 | 1;
        output2 = state.node_idx << 16 | 2;
        output3 = state.node_idx << 16 | 3;
        output4 = state.node_idx << 16 | 4;
        log::trace!("Service {} called\nval0: {}\nval1: {}\nval2: {}\nval3: {}\nval4: {}\n",
            state.node_idx, val0, val1, val2, val3, val4);
        state = NodeState {
            counter: state.counter + val0 + val1 + val2 + val3 + val4,
            ..state
        };
    }
}

// A fully connected app of 6 nodes: each node has 5 links to other services.
fn build_app() -> Application {
    let mut app_spec = Application::new();
    let nodes = (0..6)
        .map(|i| {
            waves::action!(format!("node{}", i).as_str() in app_spec
        (state: NodeState)
        (input0: Option<MsgType>,
         input1: Option<MsgType>,
         input2: Option<MsgType>,
         input3: Option<MsgType>,
         input4: Option<MsgType>)
        ->
        (output0: MsgType,
         output1: MsgType,
         output2: MsgType,
         output3: MsgType,
         output4: MsgType)
        {
            NodeState {
                counter: 0,
                node_idx: i
            }.pack().into_boxed_bitslice()
        }
        node6)
        })
        .collect::<Vec<_>>();
    waves::link!(nodes[0] output0 -> nodes[1] input0 in app_spec);
    waves::link!(nodes[0] output1 -> nodes[2] input0 in app_spec);
    waves::link!(nodes[0] output2 -> nodes[3] input0 in app_spec);
    waves::link!(nodes[0] output3 -> nodes[4] input0 in app_spec);
    waves::link!(nodes[0] output4 -> nodes[5] input0 in app_spec);

    waves::link!(nodes[1] output0 -> nodes[2] input1 in app_spec);
    waves::link!(nodes[1] output1 -> nodes[3] input1 in app_spec);
    waves::link!(nodes[1] output2 -> nodes[4] input1 in app_spec);
    waves::link!(nodes[1] output3 -> nodes[5] input1 in app_spec);
    waves::link!(nodes[1] output4 -> nodes[0] input1 in app_spec);

    waves::link!(nodes[2] output0 -> nodes[3] input2 in app_spec);
    waves::link!(nodes[2] output1 -> nodes[4] input2 in app_spec);
    waves::link!(nodes[2] output2 -> nodes[5] input2 in app_spec);
    waves::link!(nodes[2] output3 -> nodes[0] input2 in app_spec);
    waves::link!(nodes[2] output4 -> nodes[1] input2 in app_spec);

    waves::link!(nodes[3] output0 -> nodes[4] input3 in app_spec);
    waves::link!(nodes[3] output1 -> nodes[5] input3 in app_spec);
    waves::link!(nodes[3] output2 -> nodes[0] input3 in app_spec);
    waves::link!(nodes[3] output3 -> nodes[1] input3 in app_spec);
    waves::link!(nodes[3] output4 -> nodes[2] input3 in app_spec);

    waves::link!(nodes[4] output0 -> nodes[5] input4 in app_spec);
    waves::link!(nodes[4] output1 -> nodes[0] input4 in app_spec);
    waves::link!(nodes[4] output2 -> nodes[1] input4 in app_spec);
    waves::link!(nodes[4] output3 -> nodes[2] input4 in app_spec);
    waves::link!(nodes[4] output4 -> nodes[3] input4 in app_spec);

    waves::link!(nodes[5] output0 -> nodes[0] input0 in app_spec);
    waves::link!(nodes[5] output1 -> nodes[1] input1 in app_spec);
    waves::link!(nodes[5] output2 -> nodes[2] input2 in app_spec);
    waves::link!(nodes[5] output3 -> nodes[3] input3 in app_spec);
    waves::link!(nodes[5] output4 -> nodes[4] input4 in app_spec);
    app_spec
}

fn run_app(cycles: usize) {
    let app_spec = build_app();
    let mut simulation = platform::SoftwareSystemSimulation::new(&app_spec);
    for _ in 0..cycles {
        simulation.simulate_system_one_cycle(&app_spec, &mut SystemSimulationCallbacks::default());
    }
}

fn build_system(alloc_type: &RandomAllocation) -> (Application, HardwareSpec) {
    let app_spec = build_app();
    let system_spec = fat_tree(
        3,
        &NodeConfiguration::default(),
        &SwitchConfiguration {
            link_configuration: LinkConfiguration {
                frame_size: 8,
                memory_size: 1,
                ..Default::default()
            },
            ..Default::default()
        },
        &LinkConfiguration {
            memory_size: match alloc_type {
                RandomAllocation::NodesOneToOne => 4 * 5, // 4 frames per link, * 5 links
                RandomAllocation::NodesAny => 4 * 5 * 5, // 4 frames per link, 5 links, 5 nodes co-located
            },
            frame_size: 8,
            ..Default::default()
        },
    );
    (app_spec, system_spec)
}

fn simulate_app(cycles: usize, alloc_type: RandomAllocation) -> anyhow::Result<(), Error> {
    let (app_spec, system_spec) = build_system(&alloc_type);
    platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        platform::AllocationPolicy::Random(RandomAllocation::NodesOneToOne),
        None,
        2 * cycles,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties::default(),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use platform::specs::NodeSpec;
    use platform::Cycle;
    use platform::HardwareSystemSimulation;
    use platform::Inspect;
    use platform::BUFFERING_DOUBLE;
    use std::collections::HashMap;

    fn test(alloc_type: RandomAllocation) {
        let (app_spec, system_spec) = build_system(&alloc_type);
        const CYCLES: usize = 10;

        fn validate_state(
            metacycle: Cycle,
            _sim_cycle: Cycle,
            _sim: &HardwareSystemSimulation<{ BUFFERING_DOUBLE }>,
            app_spec: &Application,
            _sys_spec: &HardwareSpec,
        ) {
            // Validation is performed at odd metacycles such that all the services in the
            // previous metacycle have been run.
            if metacycle % 2 == 1 {
                let ref_app_spec = build_app();
                let mut ref_sim = platform::SoftwareSystemSimulation::new(&app_spec);
                for _ in 0..=(metacycle / 2) {
                    ref_sim.simulate_system_one_cycle(
                        &ref_app_spec,
                        &mut SystemSimulationCallbacks::default(),
                    );
                }
                let ref_node_states = ref_app_spec
                    .iter_nodes()
                    .map(|node_id| {
                        let state = ref_app_spec
                            .get_node(node_id)
                            .borrow()
                            .into_stateful_node()
                            .unwrap()
                            .persistent_state()
                            .unwrap()
                            .clone();
                        (node_id, state)
                    })
                    .collect::<HashMap<_, _>>();

                let node_states = app_spec
                    .iter_nodes()
                    .map(|node_id| {
                        let state = app_spec
                            .get_node(node_id)
                            .borrow()
                            .into_stateful_node()
                            .unwrap()
                            .persistent_state()
                            .unwrap()
                            .clone();
                        (node_id, state)
                    })
                    .collect::<HashMap<_, _>>();
                for (ref_k, ref_v) in ref_node_states.iter() {
                    assert_eq!(
                        ref_v.as_bitslice(),
                        node_states[ref_k].as_bitslice(),
                        "{:?}",
                        ref_k
                    );
                }
            }
        }

        platform::simulate_bittide(
            &system_spec,
            &[&app_spec],
            platform::AllocationPolicy::Random(alloc_type),
            Some(Inspect::HW(validate_state)),
            2 * CYCLES,
            &mut SystemSimulationCallbacks::default(),
            FailureProperties::default(),
        )
        .unwrap();
    }

    #[test]
    fn test_nodes_one_to_one() {
        env_logger::init();
        test(RandomAllocation::NodesOneToOne);
    }

    #[test]
    fn test_nodes_any() {
        test(RandomAllocation::NodesAny);
    }
}

fn main() {
    env_logger::init();
    const CYCLES: usize = 255;
    log::info!("Software simulation");
    run_app(CYCLES);
    log::info!("Hardware simulation");
    simulate_app(CYCLES, RandomAllocation::NodesOneToOne).expect("Hardware simulation failed.");
}
