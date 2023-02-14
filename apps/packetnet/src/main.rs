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

//! Implementing a packet switched network.
use std::cmp::{max, min};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::env;
use std::process;

use bits::*;
use bits_derive::*;
use bitvec::bitbox;
use platform::specs::ApplicationNode;
use platform::Application;
#[cfg(test)]
use platform::FailureProperties;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;

mod logging;
mod packet_net;

use logging::*;
pub use packet_net::*;

/// Application packet payload --- currently, empty.
#[derive(Bits)]
struct Payload {}

/// Implementation of a pretty bad PRNG. Do not use.
/// We only reimplement it because we need its state to implement Bits.
#[derive(Bits)]
struct BadPrng {
    xorshift32_state: u32,
}

impl BadPrng {
    fn new(seed: u32) -> BadPrng {
        assert_ne!(seed, 0);
        BadPrng {
            xorshift32_state: seed,
        }
    }
    fn next(&mut self) -> u32 {
        self.xorshift32_state ^= self.xorshift32_state << 13;
        self.xorshift32_state ^= self.xorshift32_state >> 17;
        self.xorshift32_state ^= self.xorshift32_state << 5;
        return self.xorshift32_state;
    }
}

/// The state of our application node.
#[derive(Bits)]
struct AppState {
    /// The network driver.
    packet_net: PacketNetState<Payload, 100>,
    /// RNG to generate our destination addresses.
    prng: BadPrng,
    /// Send messages every N cycles.
    send_period: u64,
    /// Send K messages every time.
    send_count_per_period: u32,
    /// Stop sending messages at this cycle.
    send_end: Cycle,
}

impl AppState {
    fn new(
        self_address: PacketNetAddress,
        logging: PacketNetLogHandle,
        send_period: u64,
        send_count_per_period: u32,
        send_end: Cycle,
        grid_size: GridSize,
    ) -> AppState {
        let seed = (self_address.row() * grid_size.cols) + self_address.col() + 1;
        AppState {
            packet_net: PacketNetState::new(self_address, grid_size, logging),
            prng: BadPrng::new(seed),
            send_period,
            send_count_per_period,
            send_end,
        }
    }
}

waves::action_fn! {
    app_node (state: AppState)
    (inputs: [Option<PacketNetMessage<Payload>>; 4]) -> (outputs: [Option<PacketNetMessage<Payload>>; 4]) {
        let mut packet_interface = state.packet_net.receive(inputs);
        if packet_interface.cycle().0 % state.send_period == 0 &&
            packet_interface.cycle() < state.send_end {
            for _ in 0..state.send_count_per_period {
                let random = state.prng.next();
                let payload = Payload {};
                let destination = PacketNetAddress {
                    row: random % packet_interface.grid_size().rows,
                    col: (random / packet_interface.grid_size().rows) % packet_interface.grid_size().cols,
                };
                packet_interface.send(payload, destination);
            }
        }
        outputs = packet_interface.transmit();
    }
}

fn build_app(
    grid_size: GridSize,
    send_period: u64,
    send_count_per_period: u32,
    send_end: Cycle,
) -> (Application, PacketNetLogHandle) {
    let mut app_spec = Application::new();
    let logging = PacketNetLogHandle::new();
    let mut grid = Vec::new();
    for j in 0..grid_size.rows {
        for i in 0..grid_size.cols {
            let address = PacketNetAddress { row: j, col: i };
            grid.push(waves::action!(&format!("node_{}_{}", j, i) in app_spec
                (state: AppState)
                (inputs: [Option<PacketNetMessage<Payload>>; 4]) -> (outputs: [Option<PacketNetMessage<Payload>>; 4])
                {
                    let mut data = bitbox![0; <AppState as Bits>::SIZE];
                    (AppState::new(address, logging, send_period, send_count_per_period, send_end, grid_size)).pack_to(&mut data);
                    data
                }
                app_node));
        }
    }
    for j in 0..grid_size.rows {
        for i in 0..grid_size.cols {
            let index = |delta_row: i32, delta_col: i32| {
                let row = (j as i32 + delta_row).rem_euclid(grid_size.rows as i32);
                let col = (i as i32 + delta_col).rem_euclid(grid_size.cols as i32);
                (row * grid_size.cols as i32 + col) as usize
            };
            let current = index(0, 0);
            waves::link!(grid[current] outputs[WEST] -> grid[index(0, -1)] inputs[EAST] in app_spec);
            waves::link!(grid[current] outputs[EAST] -> grid[index(0, 1)] inputs[WEST] in app_spec);
            waves::link!(grid[current] outputs[NORTH] -> grid[index(-1, 0)] inputs[SOUTH] in app_spec);
            waves::link!(grid[current] outputs[SOUTH] -> grid[index(1, 0)] inputs[NORTH] in app_spec);
        }
    }
    (app_spec, logging)
}

#[cfg(test)]
fn simulate_app(
    cycles: usize,
    grid_size: GridSize,
    send_period: u64,
    send_count_per_period: u32,
    send_end: Cycle,
) -> anyhow::Result<(Application, PacketNetLogHandle)> {
    let (app_spec, logging) = build_app(grid_size, send_period, send_count_per_period, send_end);
    let allocation =
        platform::AllocationPolicy::OneToOneNetwork(platform::MappingConfiguration1x1Network {
            frame_size: 1000,
            ..Default::default()
        });
    let system_spec = platform::generate_system_spec(&app_spec, &allocation);
    log::trace!("app graphviz:\n{}", app_spec.to_graphviz());
    log::trace!("system graphviz:\n{}", system_spec.to_graphviz());
    platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        allocation,
        None,
        2 * cycles,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties::default(),
    )?;
    Ok((app_spec, logging))
}

fn run_app(
    cycles: usize,
    grid_size: GridSize,
    send_period: u64,
    send_count_per_period: u32,
    send_end: Cycle,
) -> anyhow::Result<(Application, PacketNetLogHandle)> {
    let (app_spec, logging) = build_app(grid_size, send_period, send_count_per_period, send_end);
    let mut simulation = platform::SoftwareSystemSimulation::new(&app_spec);
    for _ in 0..cycles {
        simulation.simulate_system_one_cycle(&app_spec, &mut SystemSimulationCallbacks::default());
    }
    Ok((app_spec, logging))
}

/// Check that no messages were dropped and no messages were in flight at the end of the run.
pub(crate) fn validate_log(log: &[PacketNetLog]) {
    let mut in_flight = HashMap::new();
    for entry in log.iter() {
        match entry {
            PacketNetLog::MessageSent {
                from, from_cycle, ..
            } => {
                *in_flight.entry((from, from_cycle)).or_insert(0) += 1;
            }
            PacketNetLog::MessageDropped { .. } => panic!("Message dropped"),
            PacketNetLog::MessageReceived {
                from, from_cycle, ..
            } => match in_flight.entry((from, from_cycle)) {
                Entry::Occupied(mut o) => {
                    *o.get_mut() -= 1;
                    if *o.get() == 0 {
                        o.remove_entry();
                    }
                }
                Entry::Vacant(_) => {
                    assert!(false, "Can't find {:?} in {:?}", (from, from_cycle), log);
                }
            },
            _ => (),
        }
    }
    if let Some((from, from_cycle)) = in_flight.keys().next() {
        assert!(
            in_flight.is_empty(),
            "Message {}:{:?} in flight in {:?}",
            from,
            from_cycle,
            log
        );
    }
}

#[cfg(test)]
mod tests {
    use crate::{simulate_app, validate_log, Cycle, GridSize};

    #[test]
    fn validate() {
        env_logger::init();
        let (_, logging) =
            simulate_app(20, GridSize { rows: 6, cols: 4 }, 2, 1, Cycle(10)).unwrap();
        let log = logging.take_log();
        validate_log(&log);
    }
}

fn distance(from: PacketNetAddress, to: PacketNetAddress, grid_size: GridSize) -> u32 {
    let dist = |from: u32, to: u32, size: u32| {
        if from == to {
            return 0;
        }
        let increasing_distance = if from < to {
            to - from
        } else {
            to + size - from
        };
        let decreasing_distance = if from > to {
            from - to
        } else {
            from + size - to
        };
        min(increasing_distance, decreasing_distance)
    };
    dist(from.col(), to.col(), grid_size.cols) + dist(from.row(), to.row(), grid_size.rows)
}

fn usage() -> ! {
    eprintln!("Usage: <rows> <cols> <send-cycles> <send-period> <send-count-per-period>");
    process::exit(1);
}

/// Run the application with the given configuration and report geometric mean of message delays
/// relative to the minimum propagation delay of each message.
fn main() {
    env_logger::init();
    let args: Vec<u32> = env::args()
        .skip(1)
        .map(|arg| {
            let Ok(ret) = arg.parse() else { usage(); };
            ret
        })
        .collect();
    if args.len() < 5 {
        usage();
    }
    let grid_size = GridSize {
        rows: args[0],
        cols: args[1],
    };
    let (_, logging) = run_app(
        args[2] as usize * 100,
        grid_size,
        args[3] as u64,
        args[4],
        Cycle(args[2] as u64),
    )
    .unwrap();
    let log = logging.take_log();
    validate_log(&log);
    let mut delay_product_ln = 0.0f64;
    let mut message_count = 0f64;
    for entry in log.iter() {
        match entry {
            PacketNetLog::MessageReceived {
                from,
                from_cycle,
                to,
                to_cycle,
            } => {
                let d = max(1, distance(*from, *to, grid_size));
                let time = (to_cycle.0 - from_cycle.0) as u32;
                delay_product_ln += ((time as f64) / (d as f64)).ln();
                message_count += 1f64;
            }
            _ => (),
        }
    }
    println!(
        "Message delay geomean {}",
        (delay_product_ln / message_count).exp()
    );
}
