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

//! The simple app adapted to test multi-frequency and batching scenarios.
//!
//! The state of the node is the last sent output, used for verification.
use bits::*;
use petgraph::visit::EdgeRef;
use platform::specs::ApplicationNode;
use platform::Application;
use platform::FailureProperties;
use platform::Frequency;
use platform::Latency;
use platform::NodeSpec;
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

fn simulate_app<
    const F_NODE_SMALL_LARGE: usize,
    const F_INPUT_LINK_SMALL_LARGE: usize,
    const F_NODE_LARGE_SMALL: usize,
    const F_INPUT_LINK_LARGE_SMALL: usize,
    const FRAME_SIZE: usize,
>(
    cycles: usize,
    inspect: Option<platform::Inspect>,
    latency_input_link_small_large: usize,
    latency_input_link_large_small: usize,
    callbacks: &mut SystemSimulationCallbacks,
) -> anyhow::Result<Application> {
    let app_spec = build_app();
    let allocation_policy =
        platform::AllocationPolicy::OneToOne(platform::MappingConfiguration1x1 {
            frame_size: FRAME_SIZE,
            ..Default::default()
        });
    let mut system_spec = platform::generate_system_spec(&app_spec, &allocation_policy);
    // Modify the 1x1 mapping to alter the component frequencies.
    let nodes = system_spec
        .iter_nodes()
        .map(|node_id| (node_id, system_spec.get_node(node_id)))
        .collect::<Vec<_>>();
    let link_ids = [
        system_spec.get_input_links(nodes[0].0).next().unwrap().id(),
        system_spec.get_input_links(nodes[1].0).next().unwrap().id(),
    ];
    for (i, (_, node)) in nodes.iter().enumerate() {
        let input_link = system_spec.get_link_mut(link_ids[i]);
        if node.borrow_mut().name() == "counter_small_large" {
            node.borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_frequency(Frequency::new(F_NODE_SMALL_LARGE));
            input_link
                .into_mut_provisioned_link()
                .unwrap()
                .set_frequency(Frequency::new(F_INPUT_LINK_SMALL_LARGE));
            input_link.set_latency(Latency(latency_input_link_small_large));
        } else if node.borrow().name() == "counter_large_small" {
            node.borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_frequency(Frequency::new(F_NODE_LARGE_SMALL));
            input_link
                .into_mut_provisioned_link()
                .unwrap()
                .set_frequency(Frequency::new(F_INPUT_LINK_LARGE_SMALL));
            input_link.set_latency(Latency(latency_input_link_large_small));
        }
    }
    platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        allocation_policy,
        inspect,
        2 * cycles,
        callbacks,
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
    use platform::SystemSimulationCallbacks;
    use platform::BUFFERING_DOUBLE;

    //
    // 1-bit frame tests
    //

    #[test]
    fn validate_1_1_1_1_1() {
        validate::<1, 1, 1, 1, 1>(0, 0);
        validate::<1, 1, 1, 1, 1>(0, 1);
        validate::<1, 1, 1, 1, 1>(1, 0);
        validate::<1, 1, 1, 1, 1>(1, 1);
        validate::<1, 1, 1, 1, 1>(7, 4);
    }

    #[test]
    fn validate_5_5_5_5_1() {
        validate::<5, 5, 5, 5, 1>(0, 0);
        validate::<5, 5, 5, 5, 1>(1, 0);
        validate::<5, 5, 5, 5, 1>(0, 1);
        validate::<5, 5, 5, 5, 1>(1, 1);
        validate::<5, 5, 5, 5, 1>(10, 7);
    }

    #[test]
    fn validate_1_5_1_5_1() {
        validate::<1, 5, 1, 5, 1>(0, 0);
        validate::<1, 5, 1, 5, 1>(0, 1);
        validate::<1, 5, 1, 5, 1>(1, 0);
        validate::<1, 5, 1, 5, 1>(1, 1);
        validate::<1, 5, 1, 5, 1>(12, 7);
    }

    #[test]
    fn validate_5_1_5_1_1() {
        validate::<5, 1, 5, 1, 1>(0, 0);
        validate::<5, 1, 5, 1, 1>(0, 1);
        validate::<5, 1, 5, 1, 1>(1, 0);
        validate::<5, 1, 5, 1, 1>(1, 1);
        validate::<5, 1, 5, 1, 1>(11, 3);
    }

    #[test]
    fn validate_2_1_3_1_1() {
        validate::<2, 1, 3, 1, 1>(0, 0);
        validate::<2, 1, 3, 1, 1>(0, 1);
        validate::<2, 1, 3, 1, 1>(1, 0);
        validate::<2, 1, 3, 1, 1>(1, 1);
        validate::<2, 1, 3, 1, 1>(5, 8);
    }

    #[test]
    fn validate_2_4_3_6_1() {
        validate::<2, 4, 3, 6, 1>(0, 0);
        validate::<2, 4, 3, 6, 1>(0, 1);
        validate::<2, 4, 3, 6, 1>(1, 0);
        validate::<2, 4, 3, 6, 1>(1, 1);
        validate::<2, 4, 3, 6, 1>(3, 33);
    }

    #[test]
    fn validate_2_6_3_4_1() {
        validate::<2, 4, 3, 6, 1>(0, 0);
        validate::<2, 4, 3, 6, 1>(0, 1);
        validate::<2, 4, 3, 6, 1>(1, 0);
        validate::<2, 4, 3, 6, 1>(1, 1);
        validate::<2, 4, 3, 6, 1>(23, 12);
    }

    #[test]
    fn validate_2_3_3_3_1() {
        validate::<2, 3, 3, 3, 1>(0, 0);
        validate::<2, 3, 3, 3, 1>(0, 1);
        validate::<2, 3, 3, 3, 1>(1, 0);
        validate::<2, 3, 3, 3, 1>(1, 1);
        validate::<2, 3, 3, 3, 1>(10, 17);
    }

    #[test]
    fn validate_3_3_2_3_1() {
        validate::<3, 3, 2, 3, 1>(0, 0);
        validate::<3, 3, 2, 3, 1>(0, 1);
        validate::<3, 3, 2, 3, 1>(1, 0);
        validate::<3, 3, 2, 3, 1>(1, 1);
        validate::<3, 3, 2, 3, 1>(3, 11);
    }

    #[test]
    fn validate_1_2_3_5_1() {
        validate::<1, 2, 3, 5, 1>(0, 0);
        validate::<1, 2, 3, 5, 1>(1, 0);
        validate::<1, 2, 3, 5, 1>(0, 1);
        validate::<1, 2, 3, 5, 1>(1, 1);
        validate::<1, 2, 3, 5, 1>(12, 5);
    }

    #[test]
    fn validate_2_4_8_16_1() {
        validate::<2, 4, 8, 16, 1>(0, 0);
        validate::<2, 4, 8, 16, 1>(0, 1);
        validate::<2, 4, 8, 16, 1>(1, 0);
        validate::<2, 4, 8, 16, 1>(1, 1);
        validate::<2, 4, 8, 16, 1>(7, 43);
    }

    //
    // 2-bit frame tests
    //

    #[test]
    fn validate_1_1_1_1_2() {
        validate::<1, 1, 1, 1, 2>(0, 0);
    }

    #[test]
    fn validate_5_5_5_5_2() {
        validate::<5, 5, 5, 5, 2>(0, 0);
    }

    #[test]
    fn validate_1_5_1_5_2() {
        validate::<1, 5, 1, 5, 2>(0, 0);
    }

    #[test]
    fn validate_5_1_5_1_2() {
        validate::<5, 1, 5, 1, 2>(0, 0);
    }

    #[test]
    fn validate_2_1_3_1_2() {
        validate::<2, 1, 3, 1, 2>(0, 0);
    }

    #[test]
    fn validate_2_4_3_6_2() {
        validate::<2, 4, 3, 6, 2>(0, 0);
    }

    #[test]
    fn validate_2_6_3_4_2() {
        validate::<2, 4, 3, 6, 2>(0, 0);
    }

    #[test]
    fn validate_2_3_3_3_2() {
        validate::<2, 3, 3, 3, 2>(0, 0);
    }

    #[test]
    fn validate_3_3_2_3_2() {
        validate::<3, 3, 2, 3, 2>(0, 0);
    }

    #[test]
    fn validate_1_2_3_5_2() {
        validate::<1, 2, 3, 5, 2>(0, 0);
    }

    #[test]
    fn validate_2_4_8_16_2() {
        validate::<2, 4, 8, 16, 2>(0, 0);
    }

    //
    // 3-bit frame tests
    //

    #[test]
    fn validate_1_1_1_1_3() {
        validate::<1, 1, 1, 1, 3>(0, 0);
    }

    #[test]
    fn validate_5_5_5_5_3() {
        validate::<5, 5, 5, 5, 3>(0, 0);
    }

    #[test]
    fn validate_1_5_1_5_3() {
        validate::<1, 5, 1, 5, 3>(0, 0);
    }

    #[test]
    fn validate_5_1_5_1_3() {
        validate::<5, 1, 5, 1, 3>(0, 0);
    }

    #[test]
    fn validate_2_1_3_1_3() {
        validate::<2, 1, 3, 1, 3>(0, 0);
    }

    #[test]
    fn validate_2_4_3_6_3() {
        validate::<2, 4, 3, 6, 3>(0, 0);
    }

    #[test]
    fn validate_2_6_3_4_3() {
        validate::<2, 4, 3, 6, 3>(0, 0);
    }

    #[test]
    fn validate_2_3_3_3_3() {
        validate::<2, 3, 3, 3, 3>(0, 0);
    }

    #[test]
    fn validate_3_3_2_3_3() {
        validate::<3, 3, 2, 3, 3>(0, 0);
    }

    #[test]
    fn validate_1_2_3_5_3() {
        validate::<1, 2, 3, 5, 3>(0, 0);
    }

    #[test]
    fn validate_2_4_8_16_3() {
        validate::<2, 4, 8, 16, 3>(0, 0);
    }

    //
    // 8-bit frame tests
    //

    #[test]
    fn validate_1_1_1_1_8() {
        validate::<1, 1, 1, 1, 8>(0, 0);
    }

    #[test]
    fn validate_5_5_5_5_8() {
        validate::<5, 5, 5, 5, 8>(0, 0);
    }

    #[test]
    fn validate_1_5_1_5_8() {
        validate::<1, 5, 1, 5, 8>(0, 0);
    }

    #[test]
    fn validate_5_1_5_1_8() {
        validate::<5, 1, 5, 1, 8>(0, 0);
    }

    #[test]
    fn validate_2_1_3_1_8() {
        validate::<2, 1, 3, 1, 8>(0, 0);
    }

    #[test]
    fn validate_2_4_3_6_8() {
        validate::<2, 4, 3, 6, 8>(0, 0);
    }

    #[test]
    fn validate_2_6_3_4_8() {
        validate::<2, 4, 3, 6, 8>(0, 0);
    }

    #[test]
    fn validate_2_3_3_3_8() {
        validate::<2, 3, 3, 3, 8>(0, 0);
    }

    #[test]
    fn validate_3_3_2_3_8() {
        validate::<3, 3, 2, 3, 8>(0, 0);
    }

    #[test]
    fn validate_1_2_3_5_8() {
        validate::<1, 2, 3, 5, 8>(0, 0);
    }

    #[test]
    fn validate_2_4_8_16_8() {
        validate::<2, 4, 8, 16, 8>(0, 0);
    }

    //
    // 32-bit frame tests
    //

    #[test]
    fn validate_1_1_1_1_32() {
        validate::<1, 1, 1, 1, 32>(0, 0);
    }

    #[test]
    fn validate_5_5_5_5_32() {
        validate::<5, 5, 5, 5, 32>(0, 0);
    }

    #[test]
    fn validate_1_5_1_5_32() {
        validate::<1, 5, 1, 5, 32>(0, 0);
    }

    #[test]
    fn validate_5_1_5_1_32() {
        validate::<5, 1, 5, 1, 32>(0, 0);
    }

    #[test]
    fn validate_2_1_3_1_32() {
        validate::<2, 1, 3, 1, 32>(0, 0);
    }

    #[test]
    fn validate_2_4_3_6_32() {
        validate::<2, 4, 3, 6, 32>(0, 0);
    }

    #[test]
    fn validate_2_6_3_4_32() {
        validate::<2, 4, 3, 6, 32>(0, 0);
    }

    #[test]
    fn validate_2_3_3_3_32() {
        validate::<2, 3, 3, 3, 32>(0, 0);
    }

    #[test]
    fn validate_3_3_2_3_32() {
        validate::<3, 3, 2, 3, 32>(0, 0);
    }

    #[test]
    fn validate_1_2_3_5_32() {
        validate::<1, 2, 3, 5, 32>(0, 0);
    }

    #[test]
    fn validate_2_4_8_16_32() {
        validate::<2, 4, 8, 16, 32>(0, 0);
    }

    fn validate<
        const F_NODE_SMALL_LARGE: usize,
        const F_INPUT_LINK_SMALL_LARGE: usize,
        const F_NODE_LARGE_SMALL: usize,
        const F_INPUT_LINK_LARGE_SMALL: usize,
        const FRAME_SIZE: usize,
    >(
        latency_input_link_small_large: usize,
        latency_input_link_large_small: usize,
    ) {
        fn inspect(
            metacycle: usize,
            cycle: usize,
            _sim: &HardwareSystemSimulation<{ BUFFERING_DOUBLE }>,
            app_spec: &Application,
            _system_spec: &platform::HardwareSpec,
        ) {
            // Check the state value after the compute metacycle, i.e., in the
            // succeeding comms metacycle.
            if metacycle % 2 == 1 && cycle == 0 {
                let app_node = app_spec.get_node_by_name("counter_small_large");
                let state_small_large = u8::unpack(
                    app_node
                        .borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                assert_eq!(state_small_large as usize, metacycle / 2 + 1);
                let app_node = app_spec.get_node_by_name("counter_large_small");
                let state_large_small = u8::unpack(
                    app_node
                        .borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                assert_eq!(state_large_small as usize, metacycle / 2 + 1);
            }
        }

        let _logger = env_logger::builder().is_test(true).try_init();
        const CYCLES: usize = 255;
        let app_spec = simulate_app::<
            F_NODE_SMALL_LARGE,
            F_INPUT_LINK_SMALL_LARGE,
            F_NODE_LARGE_SMALL,
            F_INPUT_LINK_LARGE_SMALL,
            FRAME_SIZE,
        >(
            CYCLES,
            Some(Inspect::HW(inspect)),
            latency_input_link_small_large,
            latency_input_link_large_small,
            &mut SystemSimulationCallbacks::default(),
        );
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
    simulate_app::<2, 4, 8, 16, 1>(
        CYCLES,
        None,
        0,
        1,
        &mut SystemSimulationCallbacks::create_vcd_callbacks(),
    )
    .expect("Hardware simulation failed.");
}
