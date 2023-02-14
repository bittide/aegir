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

use platform::Application;
use platform::FailureProperties;
use platform::Latency;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;
use rand::random;

mod design;
use design::build_app;

const MAX_LATENCY: usize = 10;

fn run_app(cycles: usize) {
    let app_spec = build_app();
    let mut simulation = platform::SoftwareSystemSimulation::new(&app_spec);
    for _ in 0..cycles {
        simulation.simulate_system_one_cycle(&app_spec, &mut SystemSimulationCallbacks::default());
    }
}

fn simulate_app(cycles: usize, inspect: Option<platform::Inspect>) -> anyhow::Result<Application> {
    let app_spec = build_app();
    let allocation = platform::AllocationPolicy::OneToOne(platform::MappingConfiguration1x1 {
        frame_size: 1,
        ..Default::default()
    });
    let mut system_spec = platform::generate_system_spec(&app_spec, &allocation);
    // Fuzz link delays for full UGN capability.
    for link_id in system_spec.iter_links() {
        system_spec
            .get_link_mut(link_id)
            .set_latency(Latency(random::<usize>() % (MAX_LATENCY + 1)));
    }
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

fn main() {
    env_logger::init();
    const CYCLES: usize = 20;
    run_app(CYCLES);
    simulate_app(CYCLES, None).expect("Simulation failed.");
}
