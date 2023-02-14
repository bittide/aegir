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

use crate::mnist::{MnistParameters, MnistPrediction};

use bits::Bits;
use bits_derive::Bits;
use bitvec::prelude::*;
use platform::specs::{ApplicationNode, StatefulNode};
use platform::FailureProperties;
use platform::*;
use waves::*;

const NEURON_LAYER: usize = 0;
const OUTPUT_LAYER: usize = 1;
pub const N_LAYERS: usize = OUTPUT_LAYER + 1;

pub const N_INPUTS: usize = 784;
pub const N_NEURONS: usize = 128;
pub const N_OUTPUTS: usize = 10;

pub enum RunMode {
    Application,
    Simulation,
    // Tensorflow,
}

fn dotp(weights: &[f32], inputs: &[f32]) -> f32 {
    weights.iter().zip(inputs.iter()).map(|(w, i)| w * i).sum()
}

#[derive(Bits, Clone, Copy, Debug)]
struct MnistImage {
    img: [f32; N_INPUTS],
}

impl From<&[f32; N_INPUTS]> for MnistImage {
    fn from(image: &[f32; N_INPUTS]) -> Self {
        MnistImage { img: image.clone() }
    }
}

action_fn! { neuron_node_fn
             (weights: [f32; N_INPUTS], bias: f32)
             (input: MnistImage) -> (output: [f32; N_OUTPUTS]) {
                 let mut relu = dotp(&weights, &input.img) + bias;
                 if relu < 0f32 { relu = 0f32; }
                 output = [relu; N_OUTPUTS];
             }
}

action_fn! { output_node_fn
             (weights: [f32; N_NEURONS], bias: f32)
             (inputs: [f32; N_NEURONS]) -> (output: f32) {
                 let input = dotp(&weights, &inputs) + bias;
                 let div: f32 = inputs.iter().map(|x| x.exp()).sum();
                 // softmax
                 output = input.exp() / div;
             }
}

pub fn build_model(params: &MnistParameters) -> anyhow::Result<Application> {
    // build a simple nn classifier with a single neuron layer, and an
    // output layer; the neuron layer does a ReLU, and the output does a
    // softmax
    let mut model = Application::new();

    // the "flatten" layer, that takes a 28x28 image and turns it into a 784
    // output vector. Unfortunately Array2<f32> are not Bits, so we can't
    // serialize them as state. So we expect that the flattening happens
    // outside, and we simply move the state to output. Moreover, we wrap
    // the vector into a struct because if we were to pass it as a vector to
    // the neuron layer, it would be interpreted as separate links.
    //
    // TODO(cascaval): this is a shortcoming for our programming model
    // (everything needs to be serializable to bits) which prevents the use
    // of libraries.
    let source_node = action! { "source" in model
                                 (test_data: [f32; N_INPUTS]) ()
                                  -> (outputs: [MnistImage; N_NEURONS])
                                 {} /* init: we initialize the source when we call classify */
                                 {
                                     outputs = [MnistImage::from(&test_data); N_NEURONS];
                                 }
    };

    // the hidden layer
    let neuron_nodes = (0..N_NEURONS)
        .map(|node_id| {
            action! { &format!("neuron_{}", node_id) in model
                       (weights: [f32; N_INPUTS], bias: f32)
                       (input: MnistImage) -> (output: [f32; N_OUTPUTS]) {
                           type NeuronState = ([f32; N_INPUTS], f32); // ([weights], bias)
                           let mut data = bitbox![0; <NeuronState as Bits>::SIZE];
                           // need to copy to a temporary array since ndarray::ArrayBase does not implement Bits
                           let mut warr = [0f32; N_INPUTS];
                           params.weights[NEURON_LAYER]
                               .column(node_id)
                               .iter()
                               .enumerate()
                               .for_each(|(i, &v)| warr[i] = v);
                           (warr, params.biases[NEURON_LAYER][[node_id]]).pack_to(&mut data);
                           data
                       }
                       neuron_node_fn
            }
        })
        .collect::<Vec<_>>();

    for h in 0..N_NEURONS {
        link!(source_node outputs[h] -> neuron_nodes[h] input in model);
    }

    // the output layer
    let output_nodes = (0..N_OUTPUTS)
        .map(|node_id| {
            action! { &format!("output_{}", node_id) in model
                       (weights: [f32; N_NEURONS], bias: f32)
                       (inputs: [f32; N_NEURONS]) -> (output: f32) {
                           type OutputState = ([f32; N_NEURONS], f32); // ([weights], bias)
                           let mut data = bitbox![0; <OutputState as Bits>::SIZE];
                           // need to copy to a temporary array since ndarray::ArrayBase does not implement Bits
                           let mut warr = [0f32; N_NEURONS];
                           params.weights[OUTPUT_LAYER]
                               .column(node_id)
                               .iter()
                               .enumerate()
                               .for_each(|(i, &v)| warr[i] = v);
                           (warr, params.biases[OUTPUT_LAYER][[node_id]]).pack_to(&mut data);
                           data
                       }
                       output_node_fn
            }
        })
        .collect::<Vec<_>>();

    for o in 0..N_OUTPUTS {
        for h in 0..N_NEURONS {
            link!(neuron_nodes[h] output[o] -> output_nodes[o] inputs[h] in model);
        }
    }

    let sink_node = action! {"sink" in model
                             (result: MnistPrediction) (inputs: [f32; N_OUTPUTS]) -> ()
                             {
                                 let pred = MnistPrediction::default();
                                 MnistPrediction::pack(&pred).into_boxed_bitslice()
                             }
                             {
                                 let _ = result;
                                 let mut confidence = 0f32;
                                 let mut label = 0u8;
                                 for i in 0..N_OUTPUTS {
                                     if inputs[i] > confidence {
                                         confidence = inputs[i];
                                         label = i as u8;
                                     }
                                 }

                                 result = MnistPrediction { label, confidence };
                             }
    };

    for o in 0..N_OUTPUTS {
        link!(output_nodes[o] output -> sink_node inputs[o] in model);
    }

    Ok(model)
}

pub fn classify(
    model: &mut Application,
    image: &[f32],
    run_mode: &RunMode,
) -> anyhow::Result<MnistPrediction> {
    // set the input for the classifier: image data
    let mut img_data = bitbox![0; <[f32; N_INPUTS] as Bits>::SIZE];
    let mut img_arr = [0f32; N_INPUTS];
    img_arr.copy_from_slice(&image);
    img_arr.pack_to(&mut img_data);
    model
        .get_node_by_name("source")
        .borrow_mut()
        .set_persistent_state(img_data);

    // one hop for reading the data + one for each layer + one for storing the result
    const N_CYCLES: usize = N_LAYERS + 2;
    match run_mode {
        RunMode::Application => {
            let mut sim = platform::SoftwareSystemSimulation::new(&model);
            for _ in 0..N_CYCLES {
                sim.simulate_system_one_cycle(&model, &mut SystemSimulationCallbacks::default());
            }
        }
        RunMode::Simulation => {
            let allocation =
                platform::AllocationPolicy::OneToOne(platform::MappingConfiguration1x1 {
                    frame_size: 128,
                    ..Default::default()
                });
            let system_spec = platform::generate_system_spec(&model, &allocation);
            platform::simulate_bittide(
                &system_spec,
                &[&model],
                allocation,
                None,
                2 * N_CYCLES,
                &mut platform::SystemSimulationCallbacks::default(),
                FailureProperties::default(),
            )?;
        }
    }
    let res = MnistPrediction::unpack(
        &model
            .get_node_by_name("sink")
            .borrow()
            .persistent_state()
            .unwrap(),
    );

    Ok(res)
}
