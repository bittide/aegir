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

//! A simple application where two counter nodes send messages to each other.
//!
//! The state of the node is the last sent output, used for verification.
use bits::*;
use platform::specs::ApplicationNode;
use platform::Application;
use platform::FailureProperties;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;

type SmallMsgType = u8;
type LargeMsgType = u32;

waves::action_fn! {
    counter_small_large (state: u8) (input: Option<SmallMsgType>) -> (output: LargeMsgType) {
        let val = input.unwrap_or(0); // on the first cycle(s) there maybe nothing on the input link
        // compute
        let counter = val as LargeMsgType + 1;
        log::debug!(
            "counter state: {} input: {}, output: {}",
            state,
            val,
            counter
        );
        output = counter;
        state = output as u8;
    }
}

waves::action_fn! {
    counter_large_small (state: u8) (input: Option<LargeMsgType>) -> (output: SmallMsgType) {
        let val = input.unwrap_or(0); // on the first cycle(s) there maybe nothing on the input link
        // compute
        let counter = val as SmallMsgType + 1;
        log::debug!(
            "counter state: {}, input: {}, output: {}",
            state,
            val,
            counter
        );
        output = counter;
        state = output as u8;
    }
}

fn build_app() -> Application {
    let mut app_spec = Application::new();
    let node0 = waves::action!("counter_small_large" in app_spec
        (state: u8) (input: Option<SmallMsgType>) -> (output: LargeMsgType)
        { u8::pack(&0).into_boxed_bitslice() }
        counter_small_large);
    let node1 = waves::action!("counter_large_small" in app_spec
        (state: u8) (input: Option<LargeMsgType>) -> (output: SmallMsgType)
        { u8::pack(&0).into_boxed_bitslice() }
        counter_large_small);
    waves::link!(node0 output -> node1 input in app_spec);
    waves::link!(node1 output -> node0 input in app_spec);
    app_spec
}

fn run_app(cycles: usize) {
    let app_spec = build_app();
    let mut simulation = platform::SoftwareSystemSimulation::new(&app_spec);
    for _ in 0..cycles {
        simulation.simulate_system_one_cycle(&app_spec, &mut SystemSimulationCallbacks::default());
    }
}

fn simulate_app(cycles: usize, inspect: Option<platform::Inspect>) -> anyhow::Result<Application> {
    let app_spec = build_app();
    let allocation =
        platform::AllocationPolicy::OneToOneNetwork(platform::MappingConfiguration1x1Network {
            frame_size: 3,
            ..Default::default()
        });
    let system_spec = platform::generate_system_spec(&app_spec, &allocation);
    log::trace!("app graphviz:\n{}", app_spec.to_graphviz());
    log::trace!("system graphviz:\n{}", system_spec.to_graphviz());
    platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        allocation,
        inspect,
        2 * cycles,
        &mut SystemSimulationCallbacks::create_vcd_callbacks(),
        FailureProperties::default(),
    )?;
    Ok(app_spec)
}

#[cfg(test)]
mod tests {
    use crate::simulate_app;
    use bits::*;
    use env_logger;
    use platform::Application;
    use platform::HardwareSystemSimulation;
    use platform::Inspect;
    use platform::NodeSpec;
    use platform::BUFFERING_DOUBLE;

    #[test]
    fn validate() {
        fn inspect(
            metacycle: usize,
            cycle: usize,
            _sim: &HardwareSystemSimulation<{ BUFFERING_DOUBLE }>,
            app_spec: &Application,
            _system_spec: &platform::HardwareSpec,
        ) {
            if metacycle % 2 == 1 && cycle == 0 {
                let node = app_spec.get_node_by_name("counter_small_large");
                let state_small_large = u8::unpack(
                    node.borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                assert_eq!(state_small_large as usize, metacycle / 2 + 1);

                let node = app_spec.get_node_by_name("counter_large_small");
                let state_large_small = u8::unpack(
                    node.borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                assert_eq!(state_large_small as usize, metacycle / 2 + 1);
            }
        }

        env_logger::init();
        const CYCLES: usize = 255;
        let app_spec = simulate_app(CYCLES, Some(Inspect::HW(inspect)));
        assert!(app_spec.is_ok());
        let app_spec = app_spec.unwrap();
        for node_id in app_spec.iter_nodes() {
            let node = app_spec.get_node(node_id);
            let node_ref = node.borrow();
            let state = node_ref
                .into_stateful_node()
                .unwrap()
                .persistent_state()
                .unwrap();
            let state_value = u8::unpack(state);
            assert_eq!(state_value as usize, CYCLES);
        }
    }
}

fn main() {
    env_logger::init();
    const CYCLES: usize = 255;
    log::info!("Software simulation");
    run_app(CYCLES);
    log::info!("Hardware simulation");
    simulate_app(CYCLES, None).expect("Hardware simulation failed.");
}
