# waves: bittide programming DSL

Initial draft: Nov 15, 2021<br/>
Last updated: Feb 13, 2023

The bittide DSL consists of a set of macros that define individual actions (task or microservices)
and links (connections) between them. Using the DSL one may build distributed applications as a
pipeline.

## Action functions

Action functions define a function that can be reused as part of multiple nodes in the pipeline.
The macro implements the serialization and deserialization of user defined (typed) inputs, outputs,
and state to buffers (objects that implement the `bits::Bits` trait).

Syntax:

```
 action_fn!(name (states*) (inputs*) -> (outputs*) { body })
```


where, `states`, `inputs` and `outputs` are sequences of `name: type` pairs separated by ‘,’
(comma); the sequence may be empty. The `()` are required to denote an empty sequence. All types
specified for states, inputs, and outputs must be of known size (Rust `Sized`), since they need to
be serializable. For example, `usize` is not an acceptable type, since it is not `Sized` in Rust.
Use `u64` instead.

## Actions

Action definition creates a node in the Application topology and returns its handle. There are two
variants of the macro, depending whether the action function is defined inline or refers to a
function previously defined using `action_fn!`.

In the inline version, a single invocation of the macro, both declares the action function and
builds a node that will invoke it.

Syntax:

```
 action!(name [@ freq] in topology (states*) (inputs*) -> (outputs*) { init } { body })
 action!(name [@ freq] in topology (states*) (inputs*) -> (outputs*) { init } action_fn_name)
```

where,

- `name` of the action, and implicitly of the node in the underlying topology (see
  `NodeSpec::name()`). We may consider that `action! `instantiates a local variable with `name`,
  although that will constrain how we name nodes.

- `@ freq` specifies (optionally) the repeat rate for the action. By default, the repeat rate is
  1. For more details on FrequencyFactor see platform/src/spec.rs. `freq` is an expression of type
  usize.

- `topology` identifies the application specification topology

- `states, inputs, outputs`, are sequences of `name: type` pairs separated by ‘,’ (comma); the
  sequence be empty, however, the `'()'` are required for empty sequences. All types specified for
  states, inputs, and outputs must be of known size (Rust `Sized`), since they need to be
  serializable. For example, `usize` is not an acceptable type, since it is not `Sized` in Rust.
  Use `u64` instead.

- `init `is Rust code that initializes and serializes the node’s initial state, at present the
  block is expected to return a `Data` result.

- `body` is Rust code may refer to any of the defined `states, inputs, outputs.`

- `action_fn_name` is the name of a function previously defined using `action_fn!`.

An action definition allows specifying the `Option` type for inputs or outputs. This means an
action may run whether the input on that port is present or not.

Based on this definition, we construct nodes in the topology that have the number of input ports
equal to the number of inputs, and the number of output ports equal to the number of outputs. The
ports are named using the corresponding parameter name. The input/output types may also be fixed
sized arrays. In that case, the number of input/output ports is the sum of all the scalar
parameters and the lengths of the array parameters.

For example,

```
action!( my_action in my_app
        () (x: u64, y: [u8; 10], z: Option<u32>) -> (result: [u64; 2] )
        { /* init block */ }
        { /* body */ } )
```

will define an action node with 12 inputs and 2 outputs. The input ports are named `x`, `y[0]` ..
`y[9]`, and `z`. The output ports are named `result[0] `and `result[1]`.

We are duplicating the prototype definition between `action_fn!` and `action!` for two main reasons:

1. Rust macros only have access to their own set of TokenTrees. Expansion happens at parse time, so
there is no semantics associated with any of the tokens. We can't do analysis and figure out
function prototypes and parameter types (or any other semantics for that matter!). We need to
provide all the info required as part of the macro signature.

2. Moreover, `action_fn_name` is a platform::spec::Action, whose prototype is:

```
pub type Action = fn(LoopbackRef, &[InputFrameRef], &mut [OutputFrameRef]);
```

and as such, the inputs/outputs have been folded. Not that we could have figured out its signature
anyway!

## Links

Links connect ports between two nodes in the topology. Links are defined using the `link!` macro:


```
link!( src_node src_port -> dst_node dst_port [as lead] in topology)
```

where:

- `src_node` and `dst_node` are the handles returned by `action!` macro.

- `src_port` and `dst_port` are the names of the ports on the respective nodes (the name of the
  parameters as specified above).

- `topology` is the name of the `Application` pipeline being constructed.

- `as lead` denotes that the destination node is the framing lead. This is an optional annotation.
  By default the source node is the lead.


### Example

Putting it together in (see also [waves/tests/sum_array.rs])

```
fn sum_ports() -> anyhow::Result<()> {
    const N_INPUTS: usize = 5;

    /* topology:

              ____
    x[0] --- |    \       _____
    x[1] --- |     \     |     |
    x[2] --- |accum \____|sink |
    x[3] --- |      /    |     |
    x[4] --- |     /     |_____|
    en   --- |____/

    */
    let mut app_spec = Application::new();
    // declare and create the actions (nodes in app_spec).
    let accum = action!(accum in app_spec
        ()
        (x: [u64; N_INPUTS], en: Option<u64>)
        -> (sum: Option<u64>) {} {
            // Note that if y is not defined, we output None.
            sum = if let Some(_) = en {
	             Some(x.iter().sum())
                } else {
                     None
            }
	      }
    )?;
    let enable = action!(clock in app_spec (counter: u64) () -> (output: Option<u64>)
    { u64::pack(&1).into_boxed_bitslice() }
    {
        counter += 1;
        output = if counter % 2 == 0 {
	          Some(counter)
          } else {
	          None
          }
    })?;

    let input_nodes = (0..N_INPUTS)
        .map(|_| {
            action!(source in app_spec (counter: u64) () -> (output: u64)
            { u64::pack(&0).into_boxed_bitslice() }
            {
                counter += 1;
                output = counter;
            })
        })
        .collect::<anyhow::Result<Vec<_>>>()?;
    let sink = action!(action: sink (last_input: u64) (input: u64) -> ()
    { u64::pack(&0).into_boxed_bitslice() }
    {
        last_input = input;
    })?;

    // create the connections
    (0..N_INPUTS).for_each(|i| {
        // app_spec.add_link(link!(input_nodes[i] output -> accum_node x[i]));
        link!(x_i in app_spec input_nodes[i] output -> accum x[i]);
    });
    link!(en in app_spec enable output -> accum en);
    link!(output in app_spec accum sum -> sink input);

    // output the graphviz representation of the topology
    println!("{}", app_spec);

    simulate_bittide_app(&app_spec)?;

    Ok(())
}
```


## Modules

To build hierarchical topologies, we need to specify subgraphs and their interfaces. We call these
modules. With the “in topology” syntax, building a subgraph is relatively straightforward: it’s
just another topology.

**Note**: _modules are not yet implemented_.

For example:

```
let mut app1 = Application::new();
action!(n1 in app1 () (input: u64) ->  (output: u64) {} { body });
action!(n2 in app1 (state: u64) (input: u64) -> (output: u64) { init } { body });
link!(n1 output -> n2 input in app1);

let mut app2 = Application::new();
action!(n1 in app2 () (input: u64) ->  (output: u64) {} { body });
action!(n2 in app2 () (input: u64) -> (output: u64) {} { body });
action!(n3 in app2 () (inputs: [u64; 2]) -> (output: u64) {} { body });
link!(n1 output -> n3 inputs[0] in app2);
link!(n2 output -> n3 inputs[1] in app2);
```

The subgraph also provides an interface that hides the internal representation and creates to
correct connections. Therefore we propose to use `module!` as the definition of a subgraph
interface, with the following syntax:

```
module!(name in topology (inputs*) -> (outputs*))
```

and, reuse `link!` to create the internal connections. Alternatively, we may consider a separate
construct, e.g., `connect!`. Continuing our previous example to build the full topology:

```
let mut main_app = Application::new();

module!(app1 in main_app (input: u64) -> (output: u64));
link!(app1 input -> n1 input in app1);
link!(n2 output -> app1 output in app1);

// alternative with connect!
connect!(input -> n1 input in app1);
connect!(n2 output -> output in app1);

module!(app2 in main_app (inputs: [u64; 2] -> (output: u64));
link!(app2 inputs[0] -> n1 input in app2);
link!(app2 inputs[1] -> n2 input in app2);
link!(n3 output -> app2 output in app2);

// alternative with connect!
connect!(inputs[0] -> n1 input in app2);
connect!(inputs[1] -> n2 input in app2);
connect!(n3 output -> output in app2);

action!(source1 in main_app () () -> (output: u64) {} { output = rand() });
action!(source2 in main_app () () -> (output: u64) {} { output = rand() });
action!(sink in main_app (state: u64) (input: u64) -> () {} { state = input });

link!(source1 output -> app1 input in main_app);
link!(app1 output -> app2 input[0] in main_app);
link!(source2 output -> app2 input[1] in main_app);
link!(app2 output -> sink input in main_app);
```


Implementation requirements:

- a struct to represent modules that implements NodeSpec.

- connections from interface to nodes – would be nice to represent the semantic info, but these
  connections do not move data, connect inputs to inputs and outputs to outputs, so it might be
  better to connect them directly to the actual node inputs. Of course, that also means that the
  module needs to be fully defined before connected in the application. To be explored.

- platform macros changes to support the new syntax.


## Limitations

- modules are not implemented

- action frequency and framing leads are experimental attributes that, while supported by the
  syntax, have not been tested and exercised by the rest of the framework. In fact, they are hard
  to reason about. For example:

```
let n1 = action!("n1" @ 2 in app () () -> (output: u64) {} { … };
let n2 = action!("n2" @ 1 in app () (input: u64) -> () {} { … };
link!(n1 output -> n2 input as lead in app);
````

when linked with n2 as a lead, n1 producing a frame on every one of its cycles will result in lost
frames, since n2 expects it to produce a frame every other cycle.

```
link!(n1 output -> n2 input in app);
```

when linked with n2 as a follower, n1 producing a frame every one of its cycles will require n2 to
read a batch of 2 frames every cycle, even though its function definition expects a single frame.
