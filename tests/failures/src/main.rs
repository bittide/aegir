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

use crate::frame_corruption::simulate_frame_corruption;
use crate::node_crash::run_simulate_node_crash;
use std::collections::HashMap;

mod frame_corruption;
mod node_crash;

fn main() {
    env_logger::init();

    let (one_counter, two_counter) = simulate_frame_corruption(0.05);
    log::info!("One: {:?} Two: {:?}", one_counter, two_counter);

    let end_cycles = run_simulate_node_crash(
        platform::AllocationPolicy::OneToOneNetwork(platform::MappingConfiguration1x1Network {
            frame_size: 64,
            ..Default::default()
        }),
        HashMap::from([("node_1_switch".to_owned(), 2)]),
        40,
    );
    log::info!("End cycles: {:?}", end_cycles);
}
