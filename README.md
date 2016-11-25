# IMPterpreter

A simple implementation of an interpreter for IMP, written in Rust.


## Building

With Rust and Cargo installed, simply run
```
cargo build
```
in the top level directory.


## Usage

In order to interpret an IMP file, simply run
```
impterpreter FILE
```

Alternatively, there is a REPL available for testing, accessed with
```
impterpreter -r
impterpreter --repl
```