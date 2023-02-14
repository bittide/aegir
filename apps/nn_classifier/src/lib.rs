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

pub mod mnist;
pub mod nn;

#[cfg(test)]
mod tests {
    use super::{mnist, nn};
    use anyhow::Result;
    use env_logger::Target;
    use ndarray::s;
    use nn::RunMode;
    use std::fs::File;
    use std::path::Path;

    fn run_model(run_mode: &RunMode) -> Result<()> {
        let logpath = Path::new("/tmp/nn-logs");
        std::fs::create_dir_all(logpath)?;
        let logfile = match run_mode {
            RunMode::Application => File::create(logpath.join("nn_classifier.log"))?,
            RunMode::Simulation => File::create(logpath.join("nn_simulation.log"))?,
        };
        let _logger = env_logger::builder()
            .target(Target::Pipe(Box::new(logfile)))
            .is_test(true)
            .try_init();

        let data_set = mnist::load_dataset()?;
        let params = mnist::MnistModel::load_pickled_parameters(&std::path::Path::join(
            &std::env::current_dir()?,
            "tf/mnist_model/mnist_weights.pickle",
        ))?;
        let mut model = nn::build_model(&params)?;

        for img_num in 0..10 {
            let pred = nn::classify(
                &mut model,
                data_set
                    .test_data
                    .slice(s![img_num, .., ..])
                    .as_slice()
                    .unwrap(),
                &run_mode,
            )?;
            println!("{}", pred);
            assert_eq!(pred.label, data_set.test_labels[[img_num, 0]]);
        }

        Ok(())
    }

    #[test]
    fn test_bittide_model() -> Result<()> {
        run_model(&RunMode::Application)
    }

    #[test]
    fn test_bittide_hardware() -> Result<()> {
        run_model(&RunMode::Simulation)
    }
}
