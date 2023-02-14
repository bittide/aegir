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

#[test]
fn basic() -> anyhow::Result<()> {
    let mut app_spec = Application::new();

    // since we are reusing the same functions, we declare them ahead of time.
    action_fn!(sum_diff () (x: u64, y: Option<u64>) -> (sum: Option<u64>, diff: u64) {
            // Note that if y is not defined,
            // this action will not run at all.
            match y {
                Some(y_) => {
                    sum = Some(x + y_);
                    diff = x - y_;
                }
                None => {
                    // Note, since diff is a mandatory output, this line is required.
                    // On the other hand, sum is an optional output.
                    diff = x;
                }
            }
        }
    );

    // Now we can instantiate a few nodes.
    //
    // Indeed, we repeat the prototype! That is because macros only have
    // visibility inside the parse tree of their own tokens. And we need the
    // prototype of the function to create ports of appropriate sizes for
    // the nodes.
    let unit0 = action!("unit0" in app_spec
                        () (x: u64, y: Option<u64>) -> (sum: Option<u64>, diff: u64)
                        {} sum_diff);
    let unit1 = action!("unit1" in app_spec
                        () (x: u64, y: Option<u64>) -> (sum: Option<u64>, diff: u64)
                        {} sum_diff);

    // We can also define the action inline. It will create a closure.
    let counter0 = action!("counter0" in app_spec
                           (counter: u64) () -> (output: u64)
                           { u64::pack(&0).into_boxed_bitslice() }
                           {
                               counter += 1;
                               output = counter;
                           }

    );
    let counter1 = action!("counter1" in app_spec
                           (counter: u64) () -> (output: Option<u64>)
                           { u64::pack(&0).into_boxed_bitslice() }
                           {
                               counter += 1;
                               output = Some(counter);
                           }
    );

    let sink0 = action!("sink0" in app_spec (last_input: u64) (input: u64) -> ()
    { u64::pack(&0).into_boxed_bitslice() }
    {
        let _ = last_input;
        last_input = input;
    });
    let sink1 = action!("sink1" in app_spec (last_input: u64) (input: Option<u64>) -> ()
    { u64::pack(&0).into_boxed_bitslice() }
    {
        if let Some(input) = input { last_input = input; }
    });

    // Now we can link them up.
    link!(counter0 output -> unit0 x in app_spec);
    link!(counter1 output -> unit0 y in app_spec);
    link!(unit0 sum  -> unit1 x in app_spec);
    link!(unit0 diff -> unit1 y in app_spec);
    link!(unit1 sum  -> sink0 input in app_spec);
    link!(unit1 diff -> sink1 input in app_spec);

    // our topology is built, let's print it
    println!("{}", app_spec.to_graphviz());

    let mut sys_sim = platform::SoftwareSystemSimulation::new(&mut app_spec);

    const MAX_ITER: u64 = 10;
    const DELAY: u64 = 2;
    (0..MAX_ITER).for_each(|i| {
        sys_sim.simulate_system_one_cycle(&mut app_spec, &mut SystemSimulationCallbacks::default());

        if i >= DELAY {
            assert_eq!(
                <(u64,)>::unpack(
                    &app_spec
                        .get_node(sink0)
                        .borrow()
                        .persistent_state()
                        .unwrap()
                )
                .0,
                2 * (i - DELAY)
            );
            assert_eq!(
                <(u64,)>::unpack(
                    &app_spec
                        .get_node(sink1)
                        .borrow()
                        .persistent_state()
                        .unwrap()
                )
                .0,
                2 * (i - DELAY)
            );
        }
    });
    Ok(())
}
