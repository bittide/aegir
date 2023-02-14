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

fn sum_array() -> anyhow::Result<()> {
    const N_INPUTS: usize = 5;

    /* topology:

              ____
    x[0] --- |    \       _____
    x[1] --- |     \     |     |
    x[2] --- |accum \____|sink |
    x[3] --- |      /    |     |
    x[4] --- |     /     |_____|
    en   --- |____/

    */

    let mut app_spec = Application::new();

    // create the nodes
    let accum = action!("accum" in app_spec () (x: [u64; N_INPUTS], en: Option<u64>)
                -> (sum: Option<u64>) {} {
                    sum = if let Some(_) = en {
                        Some(x.iter().sum())
                    } else {
                        None
                    }
                }
    );

    let input_nodes = (0..N_INPUTS)
        .map(|i| {
            action!(&format!("x[{}]", i) in app_spec
            (counter: u64) () -> (output: u64)
            { u64::pack(&0).into_boxed_bitslice() }
            {
                counter += 1;
                output = counter;
            })
        })
        .collect::<Vec<_>>();
    let enable = action!("clock" in app_spec (counter: u64) () -> (output: Option<u64>)
    { u64::pack(&1).into_boxed_bitslice() }
    {
        counter += 1;
        output = if counter % 2 == 0 {
            Some(counter)
        } else {
            None
        }
    });
    let sink = action!("sink" in app_spec (last_input: u64) (input: Option<u64>) -> ()
    { u64::pack(&0).into_boxed_bitslice() }
    {
        #[allow(unused_assignments)]
        if let Some(input) = input {
            last_input = input;
        }
    });

    // create the connections
    (0..N_INPUTS).for_each(|i| {
        link!(input_nodes[i] output -> accum x[i] in app_spec);
    });
    link!(enable output -> accum en in app_spec);
    link!(accum sum -> sink input in app_spec);

    println!("{}", app_spec.to_graphviz());

    let mut sys_sim = platform::SoftwareSystemSimulation::new(&mut app_spec);

    const MAX_ITER: u64 = 100;
    const DELAY: u64 = 2;
    (0..MAX_ITER).for_each(|i| {
        sys_sim.simulate_system_one_cycle(&mut app_spec, &mut SystemSimulationCallbacks::default());

        log::debug!(
            "{}: {}",
            i,
            u64::unpack(&app_spec.get_node(sink).borrow().persistent_state().unwrap())
        );
        if i > DELAY {
            if i % 2 == 0 {
                assert_eq!(
                    u64::unpack(&app_spec.get_node(sink).borrow().persistent_state().unwrap()),
                    (N_INPUTS as u64) * (i - DELAY + 1)
                );
            } else {
                assert_eq!(
                    u64::unpack(&app_spec.get_node(sink).borrow().persistent_state().unwrap()),
                    (N_INPUTS as u64) * (i - DELAY)
                );
            }
        }
    });
    Ok(())
}

#[test]
fn test_sum_array() {
    sum_array().expect("Failed simulation");
}
