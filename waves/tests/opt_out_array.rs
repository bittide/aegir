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
use bits_derive::Bits;
use platform::specs::{ApplicationNode, StatefulNode};
use platform::Application;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;
use waves::*;

// Same topology as broadcast, but with optional outputs of struct type.
const N_ELEMENTS: usize = 7;

#[derive(Bits, Copy, Clone)]
struct Response {
    data: [u64; N_ELEMENTS],
}

impl Response {
    fn new(input: u64) -> Self {
        Self {
            data: [input; N_ELEMENTS],
        }
    }
}

fn optional_outputs() -> anyhow::Result<()> {
    const N_OUTPUTS: usize = 5;
    /* topology:

                  _____
     _____       /     |--- x[0]
    |     |     /      |--- x[1]
    | src |____/ bcast |--- x[2]
    |     |    \       |--- x[3]
    |_____|     \      |--- x[4]
                 ------
    */

    let mut app_spec = Application::new();

    // create the nodes
    let bcast = action!("bcast" in app_spec () (input: u64) -> (x: [Option<Response>; N_OUTPUTS]) {} {
        x = [Some(Response::new(input)); N_OUTPUTS];
    });

    let source = action!("source" in app_spec (counter: u64) () -> (output: u64)
    { u64::pack(&1).into_boxed_bitslice() }
    {
            counter += 1;
            output = counter;
    });

    // declare a "reusable" action
    action_fn!(sink (last_input: u64) (input: Option<Response>) -> () {
            #[allow(unused_assignments)]
            if let Some(response) = input {
                last_input = response.data.iter().sum();
            }
    });
    let output_nodes = (0..N_OUTPUTS)
        .map(|i| {
            action!(&format!("x[{}]", i) in app_spec
                    (last_input: u64) (input: Option<Response>) -> ()
                    { u64::pack(&0).into_boxed_bitslice() }
                    sink)
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
                    i * (N_ELEMENTS as u64)
                );
            });
        }
    });
    Ok(())
}

#[test]
fn test_opt_out_array() {
    let _logger = env_logger::builder().is_test(true).try_init();
    optional_outputs().expect("Failed simulation");
}
