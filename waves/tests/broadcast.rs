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

use bits::Bits;
use platform::specs::{ApplicationNode, StatefulNode};
use platform::Application;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;
use waves::*;

fn broadcast() -> anyhow::Result<()> {
    const N_OUTPUTS: usize = 6;

    /* topology:

                  _____
     _____       /     |--- x[0]
    |     |     /      |--- x[1]
    | src |____/ bcast |--- x[2]
    |     |    \       |--- x[3]
    |_____|     \      |--- x[4]
                 \_____|--- x[5]

    */

    let mut app_spec = Application::new();

    // create the nodes
    let bcast = action!("bcast" in app_spec () (input: u64) -> (x: [u64; N_OUTPUTS]) {} {
        x = [input; N_OUTPUTS];
    });

    let source = action!("source" in app_spec (counter: u64) () -> (output: u64)
    { u64::pack(&1).into_boxed_bitslice() }
    {
            counter += 1;
            output = counter;
    });

    // declare a "reusable" action
    action_fn!(sink (last_input: u64) (input: Option<u64>) -> () {
            #[allow(unused_assignments)]
            if let Some(input) = input {
                last_input = input;
            }
    });
    let output_nodes = (0..N_OUTPUTS)
        .map(|i| {
            action!(&format!("x[{}]", i) in app_spec
                    (last_input: u64) (input: Option<u64>) -> () 
                    { u64::pack(&0).into_boxed_bitslice() } sink)
        })
        .collect::<Vec<_>>();

    // create the connections
    link!(source output -> bcast input in app_spec);
    (0..N_OUTPUTS).for_each(|i| {
        link!(bcast x[i] -> output_nodes[i] input in app_spec);
    });

    println!("{}", app_spec.to_graphviz());

    let mut sys_sim = platform::SoftwareSystemSimulation::new(&mut app_spec);

    const MAX_ITER: u64 = 100;
    const DELAY: u64 = 2;
    (0..MAX_ITER).for_each(|i| {
        sys_sim.simulate_system_one_cycle(&mut app_spec, &mut SystemSimulationCallbacks::default());

        log::debug!(
            "{}: {}",
            i,
            u64::unpack(
                &app_spec
                    .get_node(output_nodes[2])
                    .borrow()
                    .persistent_state()
                    .unwrap()
            )
        );
        if i > DELAY {
            output_nodes.iter().for_each(|&x_i| {
                assert_eq!(
                    u64::unpack(&app_spec.get_node(x_i).borrow().persistent_state().unwrap()),
                    i
                );
            });
        }
    });
    Ok(())
}

#[test]
fn test_broadcast() {
    broadcast().expect("Failed simulation");
}
