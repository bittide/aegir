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

//! Test that specifying a frame corruption rate injects corruption on frames
//! transmitted betweeen nodes.

use bits::*;
use bits_derive::Bits;
use platform::specs::ApplicationNode;
use platform::Application;
use platform::FailureProperties;
use platform::NodeIndex;
use platform::NodeSpec;
use platform::SystemSimulationCallbacks;

const PATTERN: u32 = 0xDEADBEEF;

#[derive(Bits, Clone, Copy, Debug, PartialEq)]
pub struct Counter {
    pub corrupt: u32,
    pub correct: u32,
}

waves::action_fn! {
    count_frame_corruption
    (counter: Counter)
    (input: Option<u32>) -> (output: u32) {
        let value = input.unwrap_or(PATTERN);
        if value != PATTERN {
            log::info!("Recv corrupt");
            counter.corrupt += 1
        } else {
            log::info!("Recv correct");
            counter.correct += 1
        }
        output = PATTERN;
    }
}

fn build_app() -> Application {
    // Two nodes, which send a pattern back and forth betweeen them,
    // counting how often it gets corrupted.

    let mut app_spec = Application::new();

    let one = waves::action!(
        "one" in app_spec
        (counter: Counter)
        (input: Option<u32>) -> (output: u32)
        { Bits::pack(&Counter{corrupt: 0, correct: 0}).into_boxed_bitslice() }
        count_frame_corruption
    );

    let two = waves::action!(
        "two" in app_spec
        (counter: Counter)
        (input: Option<u32>) -> (output: u32)
        { Bits::pack(&Counter{corrupt: 0, correct: 0}).into_boxed_bitslice() }
        count_frame_corruption
    );

    waves::link!(one output -> two input in app_spec);
    waves::link!(two output -> one input in app_spec);

    app_spec
}

fn get_counter(idx: NodeIndex, app_spec: &Application) -> Counter {
    let node = app_spec.get_node(idx);
    let node_ref = node.borrow();
    let stateful_node = node_ref.into_stateful_node().unwrap();
    Counter::unpack(stateful_node.persistent_state().unwrap())
}

// Returns the counts of corrupt/correct messages received for both nodes.
pub fn simulate_frame_corruption(frame_corruption_rate: f64) -> (Counter, Counter) {
    let app_spec = build_app();
    let allocation =
        platform::AllocationPolicy::OneToOneNetwork(platform::MappingConfiguration1x1Network {
            frame_size: 4,
            ..Default::default()
        });
    let system_spec = platform::generate_system_spec(&app_spec, &allocation);
    let res = platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        allocation,
        None,
        1000,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties {
            frame_corruption_rate: frame_corruption_rate,
            // Note: default RNG behavior is deterministic.
            ..Default::default()
        },
    );
    res.expect("Failed to run bittide");

    let one_counter = get_counter(NodeIndex::new(0), &app_spec);
    let two_counter = get_counter(NodeIndex::new(1), &app_spec);

    (one_counter, two_counter)
}

#[cfg(test)]
mod tests {
    use crate::{frame_corruption::Counter, simulate_frame_corruption};

    #[test]
    fn test_frame_corruption() {
        // Test frame corruption simulation. Note: we're testing with a one to one
        // network topology, so the messages between nodes transit two switches
        // on their path to their destination, e.g.:
        //      src -> src_switch -> dst_switch -> dst
        // Every frame that passes across a link has a probability of being
        // corrupted, Pc. So the probability 1 frame transits across 3 links
        // without being corrupted is (1 - Pc)^3.
        // The messages require 8 frames, so the probability to get 8 consecutive
        // frames across three links is (1 - Pc)^(8 * 3) = (1 - Pc)^24.
        // The runs below send 500 messages, so the number of correct messages
        // we receive should expect to receive should be around 500 * (1 - Pc)^24.

        // Sanity check, with 0 corruption, our nodes should receive no corrupt frames.
        let _ = env_logger::try_init();
        let (one_counter, two_counter) = simulate_frame_corruption(0.0);
        log::info!(
            "No corruption:\tone: {:?} two: {:?}",
            one_counter,
            two_counter
        );
        assert_eq!(
            one_counter,
            Counter {
                corrupt: 0,
                correct: 500,
            }
        );

        // With a little corruption...
        // Expected correct messages: 500*(1 - 0.001)^24 = ~488.
        let (one_counter, two_counter) = simulate_frame_corruption(0.001);
        log::info!(
            "Little corruption:\tone: {:?} two: {:?}",
            one_counter,
            two_counter
        );
        assert_eq!(
            one_counter,
            Counter {
                corrupt: 13,
                correct: 487,
            }
        );

        // With some corruption...
        // Expected correct messages: 500*(1 - 0.05)^24 = ~145.
        let (one_counter, two_counter) = simulate_frame_corruption(0.05);
        log::info!(
            "Some corruption:\tone: {:?} two: {:?}",
            one_counter,
            two_counter
        );
        assert_eq!(
            one_counter,
            Counter {
                corrupt: 357,
                correct: 143,
            }
        );

        // And with a higher corruption rate...
        // Expected correct messages: 500*(1 - 0.25)^24 = ~0.5.
        let (one_counter, two_counter) = simulate_frame_corruption(0.25);
        log::info!(
            "High corruption:\tone: {:?} two: {:?}",
            one_counter,
            two_counter
        );
        assert_eq!(
            one_counter,
            Counter {
                corrupt: 498,
                correct: 2,
            }
        );
    }
}
