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

use platform::predefined::{source, stateful_sink};
use platform::specs::ApplicationNode;
use platform::{Application, FrequencyFactor, NodeSpec};
use waves::*;

// test setting the frequency factor with different expression types:
// constants, literals, and variables.
#[test]
fn action_frequency_factor_parse() {
    const FF_N1: usize = 3;
    let ff_n2 = 5;

    let mut app = Application::new();
    let n1 = action!("n1" @ FF_N1 in app
                     (counter: u64) () -> (output: u64) {} source);
    let n2 = action!("n2" @ ff_n2 in app
                     (counter: u64) (input: Option<u64>) -> () {} stateful_sink);
    let n3 = action!("n3" @ 6 in app
                     (counter: u64) (input: Option<u64>) -> () {} stateful_sink);
    link!(n1 output -> n2 input in app);
    assert_eq!(
        app.get_node(n1)
            .borrow()
            .into_application_node()
            .unwrap()
            .rate_of_service(),
        FrequencyFactor(FF_N1),
        "invalid frequency factor for n1"
    );
    assert_eq!(
        app.get_node(n2)
            .borrow()
            .into_application_node()
            .unwrap()
            .rate_of_service(),
        FrequencyFactor(ff_n2),
        "invalid frequency factor for n2"
    );
    assert_eq!(
        app.get_node(n3)
            .borrow()
            .into_application_node()
            .unwrap()
            .rate_of_service(),
        FrequencyFactor(6),
        "invalid frequency factor for n3"
    );
}

/* TODO(cascaval): support for testing compile-time errors
#[test]
#[should_panic(expected = "expected `usize`, found `&str`")]
fn action_frequency_factor_no_lit() {
    let mut app = Application::new();
    let n1 = action!("n1" @ "some_string" in app
                     (counter: u64) () -> (output: u64) source);
}
*/
