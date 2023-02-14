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
use platform::specs::ApplicationNode;
use platform::{Application, FramingLinkTrait};
use waves::*;

#[test]
fn waves() -> anyhow::Result<()> {
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

    // create the application topology
    let mut app_spec = Application::new();

    // declare an action function as a standalone function.
    action_fn!(accum_fn
        ()
        (x: [u64; N_INPUTS], en: Option<u64>)
        -> (sum: Option<u64>) {
            sum = if let Some(_) = en {
                     Some(x.iter().sum())
                } else {
                     None
            }
        }
    );

    let input_nodes = (0..N_INPUTS)
        .map(|i| {
            let name = format!("source_{}", i);
            // create an action with an inline function, with the name as an expression.
            action!(name.as_str() in app_spec (counter: u64) () -> (output: u64)
            { u64::pack(&(i as u64)).into_boxed_bitslice() }
            {
                counter += 1;
                output = counter;
            })
        })
        .collect::<Vec<platform::NodeIndex>>();
    // create an action using another inline function and the name as a static
    // string.
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
    // create an action that uses the action function define above.
    //
    // Indeed, we repeat the prototype! That is because macros only have
    // visibility inside the parse tree of their own tokens. And we need the
    // prototype of the function to create ports of appropriate sizes for
    // the nodes.
    let accum = action!("accum" in app_spec
                        () (x: [u64; N_INPUTS], en: Option<u64>) -> (sum: Option<u64>)
                        {} accum_fn);
    // create an action that uses a predefined action function.
    let sink = action!("sink" in app_spec (last_input: u64) (input: u64) -> ()
                        { u64::pack(&0).into_boxed_bitslice() }                   
                        platform::predefined::stateful_sink);

    // create the connections
    (0..N_INPUTS).for_each(|i| {
        // create a connection specifying the destination as the framing lead.
        link!(input_nodes[i] output -> accum x[i] as lead in app_spec);
    });
    app_spec
        .get_input_links(accum)
        .for_each(|edge| assert_eq!(edge.weight().framing_lead(), platform::FramingLead::Dst));
    // create links with the default FramingLead::Src
    link!(enable output -> accum en in app_spec);
    link!(accum sum -> sink input in app_spec);

    // output the graphviz representation of the topology
    println!("{}", app_spec);

    Ok(())
}
