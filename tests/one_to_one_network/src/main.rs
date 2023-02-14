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

//! A simple application for testing the OneToOneNetwork allocation policy.
//!
//! The state of the node is the last sent output, used for verification.
use bits::*;
use platform::specs::ApplicationNode;
use platform::specs::ProvisionedNode;
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
    source (state: (u8, u8)) () -> (output_small: SmallMsgType, output_large: LargeMsgType) {
        output_small = state.0 as SmallMsgType;
        output_large = state.1 as LargeMsgType;
    }

}

waves::action_fn! {
    counter_small_large
    (state: u8)
    (input: Option<SmallMsgType>, input_source: Option<SmallMsgType>) ->
    (output: LargeMsgType, output_sink: LargeMsgType) {
        // on the first cycle(s) there may be nothing on the input link
        let val = input.unwrap_or(0);
        let val_source = input_source.unwrap_or(0);
        // compute
        let counter = val as LargeMsgType + val_source as LargeMsgType;
        log::debug!(
            "counter state: {} input: {}, input_source: {}, output: {}",
            state,
            val,
            val_source,
            counter
        );
        output = counter;
        output_sink = counter;
        state = output as u8;
    }
}

waves::action_fn! {
    counter_large_small
    (state: u8)
    (input: Option<LargeMsgType>, input_source: Option<LargeMsgType>) ->
    (output: SmallMsgType, output_sink: SmallMsgType) {
         // on the first cycle(s) there may be nothing on the input link
        let val = input.unwrap_or(0);
        let val_source = input_source.unwrap_or(0);
        // compute
        let counter = val as SmallMsgType + val_source as SmallMsgType;
        log::debug!(
            "counter state: {}, input: {}, input_source: {}, output: {}",
            state,
            val,
            val_source,
            counter
        );
        output = counter;
        output_sink = counter;
        state = output as u8;
    }
}

waves::action_fn! {
    sink (state: (u8, u8)) (input_small: Option<SmallMsgType>, input_large: Option<LargeMsgType>) -> () {
        state.0 = input_small.unwrap_or(0) as u8;
        state.1 = input_large.unwrap_or(0) as u8;
    }

}

fn build_app() -> Application {
    let mut app_spec = Application::new();
    let source = waves::action!("source" in app_spec
        (state: (u8, u8))
        () ->
        (output_small: SmallMsgType, output_large: LargeMsgType)
        { Bits::pack(&(1u8, 1u8)).into_boxed_bitslice() }
        source);
    let small_large = waves::action!("counter_small_large" in app_spec
        (state: u8)
        (input: Option<SmallMsgType>, input_source: Option<SmallMsgType>) ->
        (output: LargeMsgType, output_sink: LargeMsgType)
        { u8::pack(&0).into_boxed_bitslice() }
        counter_small_large);
    let large_small = waves::action!("counter_large_small" in app_spec
        (state: u8)
        (input: Option<LargeMsgType>, input_source: Option<LargeMsgType>) ->
        (output: SmallMsgType, output_sink: SmallMsgType)
        { u8::pack(&0).into_boxed_bitslice() }
        counter_large_small);
    let sink = waves::action!("sink" in app_spec
        (state: (u8, u8))
        (input_small: Option<SmallMsgType>, input_large: Option<LargeMsgType>) ->
        ()
        { Bits::pack(&(0u8, 0u8)).into_boxed_bitslice() }
        sink);

    waves::link!(source output_small -> small_large input_source in app_spec);
    waves::link!(source output_large -> large_small input_source in app_spec);
    waves::link!(small_large output -> large_small input in app_spec);
    waves::link!(large_small output -> small_large input in app_spec);
    waves::link!(small_large output_sink -> sink input_large in app_spec);
    waves::link!(large_small output_sink -> sink input_small in app_spec);
    app_spec
}

fn run_app(cycles: usize) {
    let app_spec = build_app();
    let mut simulation = platform::SoftwareSystemSimulation::new(&app_spec);
    for _ in 0..cycles {
        simulation.simulate_system_one_cycle(&app_spec, &mut SystemSimulationCallbacks::default());
    }
}

fn simulate_app(
    cycles: usize,
    inspect: Option<platform::Inspect>,
    callbacks: &mut SystemSimulationCallbacks,
) -> anyhow::Result<Application> {
    let app_spec = build_app();
    let allocation =
        platform::AllocationPolicy::OneToOneNetwork(platform::MappingConfiguration1x1Network {
            frame_size: 3,
            ..Default::default()
        });
    let mut system_spec = platform::generate_system_spec(&app_spec, &allocation);
    // Set frequency of comms components (links+switches).
    let comms_frequency = Frequency::new(10);
    for sys_node_id in system_spec.iter_nodes() {
        if system_spec
            .get_node(sys_node_id)
            .borrow()
            .into_provisioned_switch_node()
            .is_some()
        {
            system_spec
                .get_node(sys_node_id)
                .borrow_mut()
                .set_frequency(comms_frequency);
        }
    }
    for sys_link_id in system_spec.iter_links() {
        system_spec
            .get_link_mut(sys_link_id)
            .into_mut_provisioned_link()
            .unwrap()
            .set_frequency(comms_frequency);
    }
    // Set compute node frequencies.
    system_spec
        .get_node_by_name("sink")
        .borrow_mut()
        .set_frequency(Frequency::new(2));
    system_spec
        .get_node_by_name("source")
        .borrow_mut()
        .set_frequency(Frequency::new(3));
    system_spec
        .get_node_by_name("counter_large_small")
        .borrow_mut()
        .set_frequency(Frequency::new(5));
    system_spec
        .get_node_by_name("counter_small_large")
        .borrow_mut()
        .set_frequency(Frequency::new(7));

    // Set some link latencies.
    for (i, link_id) in system_spec.iter_links().enumerate() {
        system_spec.get_link_mut(link_id).set_latency(Latency(i));
    }
    log::debug!("Application {}", app_spec.to_graphviz());
    log::debug!("HardwareSpec {}", system_spec.to_graphviz());
    platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        allocation,
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
    use platform::{
        Application, HardwareSystemSimulation, Inspect, NodeSpec, SystemSimulationCallbacks,
        BUFFERING_DOUBLE,
    };

    #[test]
    fn validate() {
        fn inspect(
            metacycle: usize,
            cycle: usize,
            _sim: &HardwareSystemSimulation<{ BUFFERING_DOUBLE }>,
            app_spec: &Application,
            _system_spec: &platform::HardwareSpec,
        ) {
            // It takes 2 metacycles for the count increment value (+1) from node:source to reach
            // each counter. Their value will remain zero until then. The count value at metacycle
            // m=2*k is therefore m / 2.
            if metacycle > 2 && metacycle % 2 == 1 && cycle == 0 {
                let node = app_spec.get_node_by_name("counter_small_large");
                let state_small_large = u8::unpack(
                    node.borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                // Since the check is performed on the *next* metacycle we use expression (metacycle - 1)
                // for checking the result.
                assert_eq!(state_small_large as usize, (metacycle - 1) / 2);

                let node = app_spec.get_node_by_name("counter_large_small");
                let state_large_small = u8::unpack(
                    node.borrow()
                        .into_stateful_node()
                        .unwrap()
                        .persistent_state()
                        .unwrap(),
                );
                assert_eq!(state_large_small as usize, (metacycle - 1) / 2);
            }
        }

        env_logger::init();
        const CYCLES: usize = 32;
        let app_spec = simulate_app(
            CYCLES,
            Some(Inspect::HW(inspect)),
            &mut SystemSimulationCallbacks::default(),
        );
        assert!(app_spec.is_ok());
        let app_spec = app_spec.unwrap();
        for node_id in app_spec.iter_nodes() {
            let node = app_spec.get_node(node_id);
            let node_ref = node.borrow();
            if node_ref.name() == "counter_large_small" || node_ref.name() == "counter_small_large"
            {
                let state = node_ref
                    .into_stateful_node()
                    .unwrap()
                    .persistent_state()
                    .unwrap();
                let state_value = u8::unpack(state);
                // Since there's an initial latency before the increment value reaches the counters,
                // the counter value only advances to CYCLES - 1.
                assert_eq!(state_value as usize, CYCLES - 1);
            }
        }
    }
}

fn main() {
    env_logger::init();
    const CYCLES: usize = 32;
    log::info!("Software simulation");
    run_app(CYCLES);
    log::info!("Hardware simulation");
    simulate_app(
        CYCLES,
        None,
        &mut SystemSimulationCallbacks::create_vcd_callbacks(),
    )
    .expect("Hardware simulation failed.");
}
