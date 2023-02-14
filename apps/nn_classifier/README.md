# Neural network

A neural network (NN) classifier implementation for bittide.

The NN is represented as a dataflow graph, with neurons as vertices and
layers fully connected.

The goal of this application is to explore the feasibility and advantages of
implementing neural networks on bittide.

## Initial implementation

The initial implementation does only inference (forward pass) using a
model pre-trained with Keras.

## Training

TODO(cascaval): implement back-prop or a different way of differentiating.

## Design

The model implements fine-grained data flow, i.e., each neuron is a node in the
bittide graph. For a mnist-inference model, that means a graph that has 3
layers, an input layer with 784 nodes (one per pixel), a hidden layer with 128
nodes with `relu` activations, and an output layer with 10 nodes with `softmax`
activation. In addition, the bittide graph has a single source node that takes
the image as a vector and distributes the pixels to each of the input nodes and
a sink node that computes the prediction.

The reason for this choice is two fold:

- it is simple: the bittide data flow graph directly matches the model; the
  functions executing on the node a mostly stateless, since for inference, the
  weights and biases are loaded at initialization time and do not change.

- with the current configuration of aegir, there isn't much that we can explore
  in terms of partitioning. For example, the paper Lünemann et al. paper,
  [Capturing Neural-Networks as Synchronous Dataflow
  Graphs](https://ieeexplore.ieee.org/document/9094536) outlines several ways of
  partitioning a model into a synchronous data flow graph, and discuss different
  trade-offs. Until we have specialized hardware nodes, I don't see how we can
  analyze any such trade-offs.

While it is unrealistic to expect that any actual implementation will map such a
fine-grained implementation directly to hardware, this is a potentially good
test for our scheduling algorithm to fold the graph into hardware nodes with
pre-defined capabilities.

The application also supports loading an existing Tensorflow model, the
nn_classified::mnist module. This is implemented mainly as a comparison
point. Just as the bittide model, it also requires a pre-trained model. However,
it does not need the custom serialization of weights required by the bittide
model.

## Dependencies

Testing the NN classifier relies on loading a pre-trained model. For
convenience, a model is saved in the repo. If you need to re-train the
model, see below.

### Keras TF model

We need to load a pre-trained model. For that, we setup and run the
[training tutorial](https://www.tensorflow.org/datasets/keras_example). The
Colab notebook is saved as [tf_mnist.py](tf/tf_mnist.py) and changed to save
the weights. This can be run locally to save the trained model as follows:

```
python3 -m pip install tensorflow tensorflow_datasets
python3 tf/tf_mnist.py
```

It saves the model in `mnist_model`.

### Data set

Unfortunately the data sets saved by TF are not usable in the mnist Rust
crate. The crate expects the [standard
format](http://yann.lecun.com/exdb/mnist/) as published by LeCun et
al. Moreover, the "download" feature of the mnist crate crashes the
execution even when not used. So we implement our own download using
`scripts/mnist_download.sh` which caches a local copy of the data set.


### Model parameters

For some reason, the TF API does not expose the model parameters (or I don't
know how to get to them!). In order to load the parameters for the bittide
model, we implement separately the serialization of weights. See
`src/mnist.rs:load_pickled_parameters`.


## Observations

- building a froward-pass data flow graph is straigthforward; building a data
  flow graph that supports both forward and backward propagation is not.

  - one could unfold the graph and build the back-prop as a continuation of the
    forward pass, but the trained weights modified in the back-prop side of the
    graph will need to be shared/communicated to the forward-prop side.

  - an alternative solution (to-be-explored) is to link the layers both forward
    and backward with optional inputs and then decide based on input
    availability whether we're doing inference or training. Not clear how we
    handle pipelining in that case. This may significantly complicate the action
    function. Q: how do TF graphs handle pipelining in this scenario?

- automating the translation of TF graphs (or even ML Pathways graphs) to
  bittide graphs would be a nice to have. This will require a library of TF
  operations as action functions, but then the actual mapping of a TF graph to
  bittide should be fairly straightforward (modulo the serialization
  requirements listed below). Alternatively, the ops could be "kernels" for
  (IREE) binary code that are invoked by the node.

- state requiring Bits for serialization is cumbersome -- however this is an
  aegir implementation decision. It is cumbersome because it is hard to reuse
  data structures defined in other crates without extending them to derive Bits,
  and then there are a number of limitations on bit arrays (see the explicit
  change for a 784 array!). We require it because we implemented nodes as
  stateless engines, and state is loaded every cycle. With the current node
  implementation this restriction could be lifted, as long as we provide some
  other mechanism of saving state to support context switching. This can be a
  separate project or lumped together with virtualization.

- bittide potential claims:

  - **performance**: our simulation runs a lot slower than TF -- obviously, the
  TF library is optimized to take advantage of processor architecture (AVX2),
  etc. A performance comparison is not fair. But this is definitely something
  that will come up, so we need to build a more convincing argument.

  - **productivity**: there are at least two aspects that we may consider,
  building the graph and scheduling the graph.

      - building the graph manually is way more involved than specifying a layer
      in Keras; this aspect may be addressed by automatically generating the
      graphs from a higher level model.

      - bittide graphs are automatically scheduled, so there is no scheduling
      work to do; however, the same is also true for Keras -- all the scheduling
      is hidden in the layers below. Pipelining comes more naturally in bittide,
      so we should explore more how we can turn it into an advantage.
