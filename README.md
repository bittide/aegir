# ægir

![](https://github.com/bittide/aegir/actions/workflows/rust.yml/badge.svg "CI passing badge")

ægir (Old Norse 'sea') is a multi-level bittide functional simulator.

ægir functionality includes:
- defining distributed applications using a simple DSL to construct
  pipelines of repeatable tasks that follow a synchronous dataflow
  programming model;
- purely functional simulation of above distributed applications;
- functional simulation of distributed applications on bittide hardware.
- initial skeleton of the allocation and scheduling system.

The current implementation represents the hardware in an idealized mode,
such that each task is executed in a single cycle and has all resources
available. We call this mode a one-to-one mapping, essentially we generate
hardware topologies that are isomorphic to the application specification.

## What is aegir?

For a longer form high level introduction to what bittide is and what aegir does, see the [aegir high level design document](DESIGN.md).

## Contributing

We'd love to accept your patches and contributions to this project.
Please see [CONTRIBUTING.md](CONTRIBUTING.md) for more details.

## Level of support

This is not an officially supported Google product.
This is an experimental prototype, developed for research purposes.

## Code organization

The code is organized in Rust crates as follows:

- `platform`: the core of the simulator, consists of the following modules:

  - `specs`: definitions of the generic objects used to construct
    topologies.

  - `app`: definition of application specific, programmer visible objects:
    Application (topology), Service (nodes) and Connection (links).

  - `hw`: definition and implementation of hardware models: HardwareSpec
    (topology), Node (hardware nodes, compute or switch), Link (links).

  - `calendar`: definition of communication calendars.

  - `scheduler`: provisioning system; allocation and scheduling.

  - `sim`: simulation support, currently ensures the correct moving of data
    over links in a bittide system.

  - `error` and `predefined`: utilities.

- `waves`: implementation of the waves DSL, the`action!`, `action_fn!`,
  `link!` and `module!` macros. See the [crate
  documentation](waves/src/lib.rs).


- `apps`: folder to develop bittide applications

  - `circuit`: an isomorphic mapping of synchronous digital logic to aegir waves

  - `exchange`: the financial exchange application.

  - `kvstore`: a canonical implementation of a key-value store.

  - `life`: Conway's way of life.

  - `nn_classifier`: mnist inference using a data-flow graph with one neuron
    per action.

  - `packetnet`: a packet network implementation on top of the bittide network.

  - `simple`: a simple application where two counter nodes send messages to each other -- the
    "hello world" for a bittide application.

  - other applications will sit here.

- `bits`

  - `bits`/`bits_derive`/`bits_test`: utility to manipulate bit vectors.
  - `schema`/`schema_derive`/`schema_test`: support modules for the bit vector
  crate.

### Build systems

`aegir` can be built using `cargo` or `blaze` (if inside Google).
Therefore, if you add a new Rust source file, it must be added to `BUILD` as
well as `Cargo.toml`. If you add a new third-party-crate dependency to
`Cargo.toml`, you will need to modify `BUILD` and possibly
import the third-party crate into Google3.

Reach out to the developers on the
[aegir channel on Discord](https://discord.gg/HcVJK4ngEb) if you need to add
a new dependency on a third-party crate.

## Projects

The following is a list of projects and ideas that can turn into
projects and are up for grabs:

| Project Name | Description | Owner|
-------------- | ----------- | -----
| hw processor models | implement execution driven simulation for a more faithful hardware model of the bittide hardware; or integrate with RTL models generated from Clash | |
| checkers           | write consistency checkers for topologies| |
| fx: sharded center | implement sharding for the exchange center | |
| fx: data store     | implement recording (txn logging) for the exchange | |
| waves: module   | implement support for hierarchical graph topologies for applications | |
| negative tests     | write negative tests throughout | |
| consensus          | define and implement a consensus protocol algorithm tailored to bittide |  |
| code exec          | define and implement a framework to execute code compiled outside Rust, e.g., neural kernels compiled with IREE | |


## Dependencies

Simply Rust. Version 1.56.1 is the minimum recommended due to
[CVE-2021-42574](https://nvd.nist.gov/vuln/detail/CVE-2021-42574). For
more details see this [ZDNet
article](https://www.zdnet.com/article/this-sneaky-trick-could-allow-attackers-to-hide-invisible-vulnerabilities-in-code/).
