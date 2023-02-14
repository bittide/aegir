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

//! The bittide DSL (waves) consists of a set of macros that define
//! individual actions (task or microservices) and links (connections)
//! between them. Using the DSL one may build distributed applications as a
//! pipeline.
//!
//! The language definition consists of:
//!
//! - an Application object that represents the application pipeline.
//! - the set of macros that enable users to express code and build the
//!   topology:
//!   - `action_fn!` defines a function that can execute as a pipeline
//!   stage (node)
//!   - `action!` defines a pipeline stage, its inputs, outputs,
//!   persistent state, and function to execute.
//!   - `link!` defines a connection between pipeline stages.
//!   - `module!` defines a grouping of several nodes and its interface.
//!
//! ## Actions
//!
//! Action definition creates a node in the Application topology and returns
//! its handle. There are two variants of the macro, depending whether the
//! action function is defined inline or refers to a function previously
//! defined using `action_fn!`.
//!
//! In the inline version, a single invocation of the macro, both declares
//! the action function and builds a node that will invoke it.
//!
//! Syntax:
//!
//! ```text
//! action!(name [@ freq] in topology (states*) (inputs*) -> (outputs*) { body })
//! action!(name [@ freq] in topology (states*) (inputs*) -> (outputs*) action_fn_name)
//! ```
//!
//! where:
//!
//! - `name` of the action, and implicitly of the node in the underlying
//! topology (yes, nodes have names, see `NodeSpec::name()`). We may
//! consider that `action! `instantiates a local variable with `name`,
//! although that will constrain how we name nodes.
//!
//! - `@ freq` specifies the repeat rate for the action. By default, the
//! repeat rate is 1.  For more details on FrequencyFactor see
//! platform/src/spec.rs. freq is an expression of type usize.
//!
//! - `topology` identifies the application specification topology
//!
//! - `states`, `inputs` and `outputs` are sequences of `name: type`
//! pairs separated by ',' (comma); the sequence may be empty. The `()` are
//! required to denote an empty sequence. All types specified for states,
//! inputs, and outputs must be of known size (Rust `Sized`), since they
//! need to be serializable. For example, `usize` is not an acceptable type,
//! since it is not `Sized` in Rust. Use `u64` instead.
//!
//! - `body` is Rust code may can refer to any of the defined `states,
//! inputs, outputs.`
//!
//! - `action_fn_name` is the name of a function previously defined using
//! `action_fn!`.
//!
//! An action definition allows specifying the `Option` type for inputs or
//! outputs. This means an action may run whether the input on that port is
//! present or not. Inputs and outputs that are not declared optional are
//! mandatory. A mandatory input that is not present in an iteration causes
//! a failure (the failure model will be defined at a later time).
//!
//! Based on this definition, we construct nodes in the topology that have a
//! number of input ports equal to the number of inputs, and a number of output
//! ports equal to the number of outputs. The ports are named using the
//! corresponding parameter name. The input/output types may also be arrays of
//! fixed size. In that case, the number of input/output ports is the sum of all
//! the scalar parameters and the lengths of the array parameters.
//! For example,
//!
//! ```text
//! action!(foo in app ()
//!                     (x: u64, y: [u8; 10], z: Option<u32>)
//!                     -> (result: [u64; 2] ) { ... } )
//! ```
//!
//! will define an action node with name `foo` in the `app` topology. The
//! node has 12 inputs and 2 outputs. The input ports are named `x`, `y[0]`
//! .. `y[9]`, and `z`. The output ports are named `result[0]` and
//! `result[1]`.
//!
//!
//! ## Action functions
//!
//! Action functions define a function that can be reused as part of
//! multiple nodes in the pipeline. The macro implements the serialization
//! and deserialization of user defined (typed) inputs, outputs, and state
//! to buffers/frames.
//!
//! Syntax:
//!
//! ```text
//! action_fn!(name (states*) (inputs*) -> (outputs*) { body })
//! ```
//!
//! The parameters for the macro are documented as part of the `action!`
//! definition above.
//!
//! ## Links
//!
//! Links connect ports between two nodes in the topology. Links are defined
//! using the `link!` macro:
//!
//! ```text
//! link!( src_node src_port -> dst_node dst_port [as lead] in topology)
//! ```
//! or
//! ```text
//! link!(name in topology src_node src_port -> dst_node dst_port [as lead])
//! ```
//! where:
//!
//! - `src_node` and `dst_node` are the handles returned by `action!` macro.
//!
//! - `src_port` and `dst_port` are the names of the ports on the respective
//!   nodes (the name of the parameters as specified above).
//!
//! - `topology` is the name of the `Application` pipeline being constructed.
//!
//! - `as lead` denotes that the destination node is the framing lead. This
//! is an optional annotation. By default the source node is the lead.
//!
//! Note that, with the second syntax variant, we introduce the ability to
//! name connections in the application specification. TODO(cascaval):
//! evaluate whether this is worth implementing.
//!
//! ### Example
//!
//! See [waves.rs](../tests/waves.rs).
//!
//! ## Modules
//!
//! To build hierarchical topologies, we need to specify subgraphs and their
//! interfaces. We call these modules. With the “in topology” syntax,
//! building a subgraph is relatively straightforward: it’s just another
//! topology. For example:
//!
//! ```text
//! let mut app1 = Application::new();
//! action!(n1 in app1 () (input: u64) ->  (output: u64) { body });
//! action!(n2 in app1 (state: u64) (input: u64) -> (output: u64) { body });
//! link!(n1 output -> n2 input in app1);
//!
//! let mut app2 = Application::new();
//! action!(n1 in app2 () (input: u64) ->  (output: u64) { body });
//! action!(n2 in app2 () (input: u64) -> (output: u64) { body });
//! action!(n3 in app2 () (inputs: [u64; 2]) -> (output: u64) { body });
//! link!(n1 output -> n3 inputs[0] in app2);
//! link!(n2 output -> n3 inputs[1] in app2);
//! ```
//!
//! The subgraph also provides an interface that hides the internal
//! representation and creates the correct connections. Therefore we propose
//! to use `module!` as the definition of a subgraph interface, with the
//! following syntax:
//!
//! ```text
//! module!(name in topology (inputs*) -> (outputs*))
//! ```
//!
//! and, reuse `link!` to create the internal connections. Alternatively, we
//! may consider a separate construct, e.g., `connect!`. Continuing our
//! previous example to build the full topology:
//!
//! ```text
//!     ... continued from above ...
//! let mut main_app = Application::new();
//!
//! module!(app1 in main_app (input: u64) -> (output: u64));
//! link!(app1 input -> n1 input in app1);
//! link!(n2 output -> app1 output in app1);
//!
//! // alternative with connect!
//! connect!(input -> n1 input in app1);
//! connect!(n2 output -> output in app1);
//!
//! module!(app2 in main_app (inputs: [u64; 2] -> (output: u64));
//! link!(app2 inputs[0] -> n1 input in app2);
//! link!(app2 inputs[1] -> n2 input in app2);
//! link!(n3 output -> app2 output in app2);
//!
//! // alternative with connect!
//! connect!(inputs[0] -> n1 input in app2);
//! connect!(inputs[1] -> n2 input in app2);
//! connect!(n3 output -> output in app2);
//!
//! action!(source1 in main_app () () -> (output: u64) { output = rand() });
//! action!(source2 in main_app () () -> (output: u64) { output = rand() });
//! action!(sink in main_app (state: u64) (input: u64) -> () { state = input });
//!
//! link!(source1 output -> app1 input in main_app);
//! link!(app1 output -> app2 input[0] in main_app);
//! link!(source2 output -> app2 input[1] in main_app);
//! link!(app2 output -> sink input in main_app);
//! ```
//!

extern crate proc_macro;
mod action;
mod action_fn;
mod link;
mod module;
mod util;

#[proc_macro]
pub fn action(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    action::action(tokens)
}

#[proc_macro]
pub fn action_fn(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    action_fn::action_fn(tokens)
}

#[proc_macro]
pub fn link(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    link::link(tokens)
}

#[proc_macro]
pub fn module(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    module::module(tokens)
}
