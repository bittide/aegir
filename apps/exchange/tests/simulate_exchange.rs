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

use env_logger::Target;
use platform::RandomAllocation;
use std::fs::File;
use std::path::Path;

use exchange::exchange::build_exchange;
use platform::AllocationPolicy;
use platform::FailureProperties;
use platform::MappingConfiguration1x1;
use platform::MappingConfiguration1x1Network;
use platform::SystemSimulationCallbacks;

const FRAME_SIZE: usize = 256;
const IO_MEMORY_SIZE: usize = 2048;

pub fn simulate_exchange_app_1x1(
    logname: &str,
    cycles: usize,
    rng_seed: Option<&str>,
) -> anyhow::Result<()> {
    let exchange_spec = build_exchange(logname, rng_seed)?;
    let allocation = AllocationPolicy::OneToOne(MappingConfiguration1x1 {
        frame_size: FRAME_SIZE,
        io_memory_size: IO_MEMORY_SIZE,
        ..Default::default()
    });
    let exchange_system = platform::generate_system_spec(&exchange_spec, &allocation);
    platform::simulate_bittide(
        &exchange_system,
        &[&exchange_spec],
        allocation,
        None,
        2 * cycles,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties::default(),
    )?;
    Ok(())
}

pub fn simulate_exchange_app_1x1_network(
    logname: &str,
    cycles: usize,
    rng_seed: Option<&str>,
) -> anyhow::Result<()> {
    let exchange_spec = build_exchange(logname, rng_seed)?;
    let allocation = AllocationPolicy::OneToOneNetwork(MappingConfiguration1x1Network {
        frame_size: FRAME_SIZE,
        io_memory_size: IO_MEMORY_SIZE,
        ..Default::default()
    });
    let exchange_system = platform::generate_system_spec(&exchange_spec, &allocation);
    platform::simulate_bittide(
        &exchange_system,
        &[&exchange_spec],
        allocation,
        None,
        2 * cycles,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties::default(),
    )?;
    Ok(())
}

pub fn simulate_exchange_app_1x1_fat_tree(
    logname: &str,
    cycles: usize,
    rng_seed: Option<&str>,
) -> anyhow::Result<()> {
    let exchange_spec = build_exchange(logname, rng_seed)?;
    let frame_size = FRAME_SIZE;
    let node_count = exchange::exchange::TRADER_COUNT + /* center */ 1;
    let mut tree_height = 1;
    while 2usize.pow(tree_height) < node_count {
        tree_height += 1;
    }
    let exchange_system = platform::fat_tree(
        tree_height as usize,
        &platform::NodeConfiguration::default(),
        &platform::SwitchConfiguration {
            link_configuration: platform::LinkConfiguration {
                frame_size: frame_size,
                ..Default::default()
            },
            ..Default::default()
        },
        &platform::LinkConfiguration {
            memory_size: IO_MEMORY_SIZE * exchange::exchange::TRADER_COUNT,
            frame_size: frame_size,
            ..Default::default()
        },
    );
    platform::simulate_bittide(
        &exchange_system,
        &[&exchange_spec],
        AllocationPolicy::Random(RandomAllocation::NodesOneToOne),
        None,
        2 * cycles,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties::default(),
    )?;
    Ok(())
}

/// Virtualizes nodes and links on a fat tree network.
pub fn simulate_exchange_app_fat_tree(
    logname: &str,
    cycles: usize,
    rng_seed: Option<&str>,
) -> anyhow::Result<()> {
    let exchange_spec = build_exchange(logname, rng_seed)?;
    let frame_size = FRAME_SIZE;
    let node_count = exchange::exchange::TRADER_COUNT + /* center */ 1;
    // The HW topology size is independent of the application size, a constant, here.
    let tree_height = 3;
    // The node_count is used to assert that the test will exercise mapping multiple
    // application nodes to a compute node.
    assert!(2usize.pow(tree_height) < node_count);
    let exchange_system = platform::fat_tree(
        tree_height as usize,
        &platform::NodeConfiguration::default(),
        &platform::SwitchConfiguration {
            link_configuration: platform::LinkConfiguration {
                frame_size: frame_size,
                ..Default::default()
            },
            ..Default::default()
        },
        &platform::LinkConfiguration {
            memory_size: IO_MEMORY_SIZE * exchange::exchange::TRADER_COUNT,
            frame_size: frame_size,
            ..Default::default()
        },
    );
    platform::simulate_bittide(
        &exchange_system,
        &[&exchange_spec],
        AllocationPolicy::Random(RandomAllocation::NodesAny),
        None,
        2 * cycles,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties::default(),
    )?;
    Ok(())
}

#[test]
fn test_run_exchange_1x1() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile = File::create(logpath.join("simulate_exchange_app_1x1.log"))
        .expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    simulate_exchange_app_1x1("sim_exchange_app_10_1x1.log", CYCLES, None)
        .expect("Failed simulation");
}

#[test]
fn test_run_exchange_1x1_network() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile = File::create(logpath.join("simulate_exchange_app_1x1_network.log"))
        .expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    simulate_exchange_app_1x1_network("sim_exchange_app_10_1x1_network.log", CYCLES, None)
        .expect("Failed simulation");
}

#[test]
fn test_run_exchange_1x1_fat_tree() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile = File::create(logpath.join("simulate_exchange_app_1x1_fat_tree.log"))
        .expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    simulate_exchange_app_1x1_fat_tree("sim_exchange_app_10_1x1_fat_tree.log", CYCLES, None)
        .expect("Failed simulation");
}

#[test]
fn test_run_exchange_fat_tree() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile = File::create(logpath.join("simulate_exchange_app_fat_tree.log"))
        .expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    simulate_exchange_app_fat_tree("sim_exchange_app_10_fat_tree.log", CYCLES, None)
        .expect("Failed simulation");
}
