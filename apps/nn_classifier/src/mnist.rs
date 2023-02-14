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

use crate::nn::N_LAYERS;

use anyhow::{bail, Result};
use bits_derive::Bits;
use mnist::*;
use ndarray::prelude::*;
use serde::Deserialize;
use serde::Serialize;
use serde_pickle;
use std::fmt;
use std::path::Path;
use std::process::Command;

pub struct MnistDataset {
    pub test_data: Array3<f32>,
    pub test_labels: Array2<u8>,
    // TODO: enable when implementing training
    // train_data: Array3<f32>,
    // train_labels: Array2<u8>,
}

/// Load the mnist data set
/// mnist data formats: http://yann.lecun.com/exdb/mnist/
pub fn load_dataset() -> Result<MnistDataset> {
    // sum of these must be < 70,000
    const N_TRAIN: usize = 0; // 60_000;
    const N_TEST: usize = 10_000;
    const N_VALIDATE: usize = 0;

    // download the dataset if not present
    // Note: the mnist crate has a download feature, but it crashes the
    // application, regardless whether it is used or not
    let download = Command::new("scripts/mnist_download.sh").output()?;
    if !download.status.success() {
        bail!("Failed to download data set");
    }

    let NormalizedMnist {
        trn_img: _,
        trn_lbl: _,
        tst_img,
        tst_lbl,
        ..
    } = MnistBuilder::new()
        .base_path("data_sets/mnist")
        .label_format_digit()
        .training_set_length(N_TRAIN as u32)
        .validation_set_length(N_VALIDATE as u32)
        .test_set_length(N_TEST as u32)
        .finalize()
        .normalize();

    /* For inference we do not need the training; that will change when we implement backprop.

    let train_data = Array3::from_shape_vec((N_TRAIN, 28, 28), trn_img)
        .expect("Error converting images to Array3 struct");
    println!("{:#.1?}\n", train_data.slice(s![image_num, .., ..]));

    let train_labels: Array2<f32> = Array2::from_shape_vec((N_TRAIN, 1), trn_lbl)
        .expect("Error converting training labels to Array2 struct")
        .map(|x| *x as f32);
    (0..10).for_each(|image_num| {
        println!(
            "The {}th digit is a {:?}",
            image_num,
            train_labels.slice(s![image_num, ..])
        )
    });
    */
    Ok(MnistDataset {
        test_data: Array3::from_shape_vec((N_TEST, 28, 28), tst_img)?,
        test_labels: Array2::from_shape_vec((N_TEST, 1), tst_lbl)?,
    })
}

/// container for the weights and biases of a trained model.
// Note: this is initialized by reading the weights from a separate weights
// file, since I couldn't figure out how to access them directly from the
// TF model.
pub struct MnistParameters {
    pub weights: [Array2<f32>; N_LAYERS],
    pub biases: [Array1<f32>; N_LAYERS],
}

impl Default for MnistParameters {
    fn default() -> Self {
        Self {
            weights: [
                // array does not implement copy ... bummer!
                Array2::<f32>::ones((1, 1)),
                Array2::<f32>::ones((1, 1)),
            ],
            biases: [Array1::<f32>::zeros(1), Array1::<f32>::zeros(1)],
        }
    }
}

#[derive(Bits)]
pub struct MnistPrediction {
    pub label: u8,
    pub confidence: f32,
}

impl fmt::Display for MnistPrediction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "predicted {} with confidence {}",
            self.label, self.confidence
        )
    }
}

impl Default for MnistPrediction {
    fn default() -> Self {
        MnistPrediction {
            label: 0,
            confidence: 0.0,
        }
    }
}

pub struct MnistModel {}

impl MnistModel {
    pub fn load_pickled_parameters(file_name: &Path) -> anyhow::Result<MnistParameters> {
        let weights_file = Path::new(file_name);
        if !weights_file.exists() {
            anyhow::bail!(
                "{} does not exist.\nPlease make sure that you ran the tf/tf_mnist.py script",
                file_name.display()
            );
        }
        let payload = std::fs::read(weights_file)?;

        #[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
        pub struct MnistPickleParameters {
            weight_shapes: Vec<Vec<i32>>,
            bias_shapes: Vec<Vec<i32>>,
            weights: Vec<Vec<f64>>,
            biases: Vec<Vec<f64>>,
        }

        // PRINT SOME DEBUGGING STUFF...
        log::debug!("Gonna deserialize!");
        let val: MnistPickleParameters =
            serde_pickle::from_slice(&payload, serde_pickle::DeOptions::new())?;
        log::debug!("weight shapes: {:?}", val.weight_shapes);
        log::debug!("bias shapes: {:?}", val.bias_shapes);
        log::debug!(
            "weight tensors (#elements): {:?}",
            &val.weights.iter().map(|w| w.len()).collect::<Vec<_>>()
        );
        log::debug!(
            "bias tensors (#elements):: {:?}",
            &val.biases.iter().map(|b| b.len()).collect::<Vec<_>>()
        );
        log::debug!("deserialized");

        let mut parameters = MnistParameters::default();
        for layer in 0..val.weight_shapes.len() {
            match val.weight_shapes[layer].len() {
                2 => {
                    parameters.weights[layer] = ArrayView::from_shape(
                        val.weight_shapes[layer]
                            .iter()
                            .map(|x| *x as usize)
                            .collect::<Vec<usize>>(),
                        &val.weights[layer]
                            .iter()
                            .map(|x| *x as f32)
                            .collect::<Vec<f32>>(),
                    )?
                    .into_owned()
                    .into_dimensionality::<ndarray::Ix2>()?;
                    parameters.biases[layer] = ArrayView::from_shape(
                        val.bias_shapes[layer]
                            .iter()
                            .map(|x| *x as usize)
                            .collect::<Vec<usize>>(),
                        &val.biases[layer]
                            .iter()
                            .map(|x| *x as f32)
                            .collect::<Vec<f32>>(),
                    )?
                    .into_owned()
                    .into_dimensionality::<ndarray::Ix1>()?;
                }
                _ => panic!("Pickled layer weights should have 0 or 2 dimensions!"),
            }
        }
        Ok(parameters)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nn::{N_INPUTS, N_LAYERS, N_NEURONS, N_OUTPUTS};

    #[test]
    fn read_pickled_weights() -> anyhow::Result<()> {
        let _logger = env_logger::builder().is_test(true).try_init();

        let params =
            MnistModel::load_pickled_parameters(&Path::new("tf/mnist_model/mnist_weights.pickle"))?;
        let w_shapes = vec![[N_INPUTS, N_NEURONS], [N_NEURONS, N_OUTPUTS]];
        let b_shapes = vec![[N_NEURONS], [N_OUTPUTS]];

        for layer in 0..N_LAYERS {
            assert_eq!(params.weights[layer].shape(), w_shapes[layer]);
            assert_eq!(params.biases[layer].shape(), b_shapes[layer]);
        }
        Ok(())
    }
}
