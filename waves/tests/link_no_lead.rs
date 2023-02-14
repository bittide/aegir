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

// TODO(cascaval): setup testing framework to check for compile-time errors.

/*
use platform::predefined::{source, stateful_sink};
use waves::*;

// should-fail
fn link_no_lead() {
    let app = platform::Application::new();
    let n1 = action!(source in app
                     (counter: u64) () -> (output: u64) source);
    let n2 = action!(sink in app
                     (counter: u64) (input: Option<u64>) -> () stateful_sink);
    link!(n1 output -> n2 input as framing_lead in app); //- ERROR expected 'lead'
}

*/
