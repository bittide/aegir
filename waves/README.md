# waves: a bittide DSL

This crate provides macros that make the `abstract_topology` easier to specify.

See the example in `./tests/simple.rs`.


## Debugging

Debugging Rust macros is involved!

There are tools that can help. Using [cargo
expand](https://github.com/dtolnay/cargo-expand) to inspect the generated
code is helpful. Once installed, you can expand an existing test as follows:

```
cargo expand --test array_port
```

While it is unlikely that you can directly compile the output, it can give
you a good hint on where to look (e.g., missing a comma to separate the
elements of a vector!).
