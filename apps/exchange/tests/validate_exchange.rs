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
use std::collections::HashMap;
use std::fs::File;
use std::path::Path;
use std::process::Command;

mod simulate_exchange;

// runs the exchange as an app and in simulation.
#[test]
fn validate_exchange_1x1() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile = File::create(logpath.join("validate_exchange_app_1x1.log"))
        .expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    let files: HashMap<&str, &str> = [
        ("run", "validate_run_10_1x1.log"),
        ("sim_1x1", "validate_sim_10_1x1.log"),
    ]
    .iter()
    .cloned()
    .collect();

    exchange::exchange::run_exchange_app(files.get("run").unwrap(), CYCLES, None)
        .expect("Failed to run application");
    simulate_exchange::simulate_exchange_app_1x1(files.get("sim_1x1").unwrap(), CYCLES, None)
        .expect("Failed to run simulation");

    // test that the test produces proper output on failure: either when no
    // file was produced, or one of the files differs. Since this is just
    // local debugging I did not want a separate test.
    //
    // std::fs::remove_file(std::path::Path::new(files.get("sim").unwrap()))
    //     .expect("Failed removing");
    // use std::io::Write;
    // std::fs::OpenOptions::new()
    //     .append(true)
    //     .open(files.get("sim").unwrap())
    //     .unwrap()
    //     .write_all(b"\n\n\n\nfail the diff\n")
    //     .expect("Failed to append to file");

    let diff_1x1 = Command::new("diff")
        .args(&vec![
            files.get("run").unwrap(),
            files.get("sim_1x1").unwrap(),
        ])
        .output()
        .expect("Failed to run diff");

    assert!(
        diff_1x1.status.success(),
        "diff_1x1 {} {} failed:\n{}\n{}",
        files.get("run").unwrap(),
        files.get("sim_1x1").unwrap(),
        String::from_utf8(diff_1x1.stdout).unwrap().to_string(),
        String::from_utf8(diff_1x1.stderr).unwrap().to_string()
    );
}

// runs the exchange as an app and in simulation.
#[test]
fn validate_exchange_1x1_network() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile = File::create(logpath.join("validate_exchange_app_1x1_network.log"))
        .expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    let files: HashMap<&str, &str> = [
        ("run", "validate_run_10_1x1_network.log"),
        ("sim_1x1_network", "validate_sim_10_1x1_network.log"),
    ]
    .iter()
    .cloned()
    .collect();

    exchange::exchange::run_exchange_app(files.get("run").unwrap(), CYCLES, None)
        .expect("Failed to run application");
    simulate_exchange::simulate_exchange_app_1x1_network(
        files.get("sim_1x1_network").unwrap(),
        CYCLES,
        None,
    )
    .expect("Failed to run simulation");

    let diff_1x1_network = Command::new("diff")
        .args(&vec![
            files.get("run").unwrap(),
            files.get("sim_1x1_network").unwrap(),
        ])
        .output()
        .expect("Failed to run diff");

    assert!(
        diff_1x1_network.status.success(),
        "diff_1x1_network {} {} failed:\n{}\n{}",
        files.get("run").unwrap(),
        files.get("sim_1x1_network").unwrap(),
        String::from_utf8(diff_1x1_network.stdout)
            .unwrap()
            .to_string(),
        String::from_utf8(diff_1x1_network.stderr)
            .unwrap()
            .to_string()
    );
}

// runs the exchange as an app and in simulation.
#[test]
fn validate_exchange_1x1_fat_tree() {
    let logpath = Path::new("/tmp/fx-logs");
    std::fs::create_dir_all(logpath)
        .expect(&format!("Failed to create logs dir: {}", logpath.display()));
    let logfile = File::create(logpath.join("validate_exchange_app_1x1_fat_tree.log"))
        .expect("Failed to create log file");
    let _logger = env_logger::builder()
        .target(Target::Pipe(Box::new(logfile)))
        .is_test(true)
        .try_init();

    const CYCLES: usize = 10;
    let files: HashMap<&str, &str> = [
        ("run", "validate_run_10_1x1_fat_tree.log"),
        ("sim_1x1_fat_tree", "validate_sim_10_1x1_fat_tree.log"),
    ]
    .iter()
    .cloned()
    .collect();

    exchange::exchange::run_exchange_app(files.get("run").unwrap(), CYCLES, None)
        .expect("Failed to run application");
    simulate_exchange::simulate_exchange_app_1x1_fat_tree(
        files.get("sim_1x1_fat_tree").unwrap(),
        CYCLES,
        None,
    )
    .expect("Failed to run simulation");

    let diff_1x1_fat_tree = Command::new("diff")
        .args(&vec![
            files.get("run").unwrap(),
            files.get("sim_1x1_fat_tree").unwrap(),
        ])
        .output()
        .expect("Failed to run diff");

    assert!(
        diff_1x1_fat_tree.status.success(),
        "diff_1x1_fat_tree {} {} failed:\n{}\n{}",
        files.get("run").unwrap(),
        files.get("sim_1x1_fat_tree").unwrap(),
        String::from_utf8(diff_1x1_fat_tree.stdout)
            .unwrap()
            .to_string(),
        String::from_utf8(diff_1x1_fat_tree.stderr)
            .unwrap()
            .to_string()
    );
}
