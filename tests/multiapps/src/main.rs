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

//! Multiple apps being hosted on the same architecture.
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
use rand;
use serde::Serialize;

type MsgType = u32;
const MAX_THRESHOLD: u32 = 100;

#[derive(Clone, Debug, Serialize, Bits)]
struct NodeState {
    counter: u32,
    threshold: u32,
    node_idx: u32,
}

waves::action_fn! {
    node6
    (state: NodeState)
    (input0: Option<MsgType>,
     input1: Option<MsgType>)
    ->
    (output0: MsgType,
     output1: MsgType) {
        let val0 = input0.map(|_| 1).unwrap_or(0);
        let val1 = input1.map(|_| 1).unwrap_or(0);
        output0 = state.node_idx << 16 | 0;
        output1 = state.node_idx << 16 | 1;
        let next_count =  state.counter + val0 + val1;
        state = NodeState {
            counter: if state.counter < state.threshold { next_count } else { state.counter },
            ..state
        };
    }
}

fn build_app() -> Application {
    let mut app_spec = Application::new();
    let nodes = (0..3)
        .map(|i| {
            waves::action!(format!("node{}", i).as_str() in app_spec
        (state: NodeState)
        (input0: Option<MsgType>,
         input1: Option<MsgType>)
        ->
        (output0: MsgType,
         output1: MsgType)
        {
            NodeState {
                counter: 0,
                threshold: rand::random::<u32>() % MAX_THRESHOLD,
                node_idx: i
            }.pack().into_boxed_bitslice()
        }
        node6)
        })
        .collect::<Vec<_>>();
    waves::link!(nodes[0] output0 -> nodes[1] input0 in app_spec);
    waves::link!(nodes[0] output1 -> nodes[2] input0 in app_spec);

    waves::link!(nodes[1] output0 -> nodes[2] input1 in app_spec);
    waves::link!(nodes[1] output1 -> nodes[0] input1 in app_spec);

    waves::link!(nodes[2] output0 -> nodes[0] input0 in app_spec);
    waves::link!(nodes[2] output1 -> nodes[1] input1 in app_spec);
    app_spec
}

fn build_system(app_count: usize) -> (Vec<Application>, HardwareSpec) {
    let apps = (0..app_count).map(|_| build_app()).collect::<Vec<_>>();
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
            memory_size: 1 << 20,
            frame_size: 8,
            ..Default::default()
        },
    );
    (apps, system_spec)
}

fn simulate_app(
    app_count: usize,
    cycles: usize,
    alloc_type: RandomAllocation,
) -> anyhow::Result<(), Error> {
    let (apps, system_spec) = build_system(app_count);
    platform::simulate_bittide(
        &system_spec,
        apps.iter().collect::<Vec<_>>().as_slice(),
        platform::AllocationPolicy::Random(alloc_type),
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
    use platform::specs::StatefulNode;

    #[test]
    fn test_apps_reaching_threshold() {
        const APP_COUNT: usize = 20;
        let (apps, system_spec) = build_system(APP_COUNT);
        // Each time a node is run its counter is incremented by two (+2).
        // Since the threshold for each counter is [0, MAX_THRESHOLD) then in the
        // worst case each application must have ceil(MAX_THRESHOLD / 2) compute
        // passes, i.e.,
        //
        // RequiredComputePasses = (MAX_THRESHOLD + 1)/2
        //
        // - For apps starting in metacycle 0
        //
        //   Since there are 2 metacycles per step (Compute+Comms), we require 2*RequiredComputePasses
        //   total metacycles, i.e., MAX_THRESHOLD + 2 metacycles. Also, since we don't need the final
        //   comms pass, they will finish in MAX_THREDHOLD + 2 - 1 = MAX_THRESHOLD + 1 metacycles.
        //
        // - For apps starting in metacycle 1,
        //   A total of 1 + (MAX_THRESHOLD + 1) = MAX_THRESHOLD + 2 metacycles are required.
        //
        // A maximum of MAX_THRESHOLD + 2 metacycles guarantees all apps saturate their threshold.
        const CYCLES: usize = 102;
        let sim_result = platform::simulate_bittide(
            &system_spec,
            apps.iter().collect::<Vec<_>>().as_slice(),
            platform::AllocationPolicy::Random(RandomAllocation::NodesAny),
            None,
            CYCLES,
            &mut SystemSimulationCallbacks::default(),
            FailureProperties::default(),
        );
        assert!(sim_result.is_ok());
        for app in apps {
            for app_node_id in app.iter_nodes() {
                let state_bits = app
                    .get_node(app_node_id)
                    .borrow()
                    .persistent_state()
                    .unwrap()
                    .clone();
                let state = NodeState::unpack(&state_bits);
                assert!(
                    state.counter >= state.threshold,
                    "counter: {}, threshold: {}",
                    state.counter,
                    state.threshold
                );
            }
        }
    }
}

fn main() {
    env_logger::init();
    const CYCLES: usize = MAX_THRESHOLD as usize + 1;
    simulate_app(1, CYCLES, RandomAllocation::NodesAny).expect("Hardware simulation failed.");
}
