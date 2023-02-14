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

use nn_classifier::{mnist, nn};

fn main() -> anyhow::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let usage = "Usage: nn_classifier <test id>, where test id is an integer < 10,000";
    assert_eq!(args.len(), 2, "{}", usage);
    let img_num = args[1].parse::<usize>().expect(usage);
    assert!(img_num < 10_000, "{}", usage);

    let data_set = mnist::load_dataset()?;
    let params = mnist::MnistModel::load_pickled_parameters(&std::path::Path::join(
        &std::env::current_dir()?,
        "tf/mnist_model/mnist_weights.pickle",
    ))?;
    let mut model = nn::build_model(&params)?;

    let pred = nn::classify(
        &mut model,
        data_set
            .test_data
            .slice(ndarray::s![img_num, .., ..])
            .as_slice()
            .unwrap(),
        &nn::RunMode::Application,
    )?;
    println!("{}", pred);

    let pred = nn::classify(
        &mut model,
        data_set
            .test_data
            .slice(ndarray::s![img_num, .., ..])
            .as_slice()
            .unwrap(),
        &nn::RunMode::Simulation,
    )?;
    println!("{} (simulated)", pred);
    Ok(())
}
