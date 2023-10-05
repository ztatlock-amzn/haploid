# haploid

Speed up SMT via preprocessing using [egg](https://egraphs-good.github.io/).


## Cargo / Rust

This project is made to be used with the standard `cargo` build system.

The easiest way to get Rust is through the [startup guide](https://www.rust-lang.org/learn/get-started).


## Building

Haploid can be built with

```
cargo build --release
```

This will create a optimized executables in `./target/release`


## Running

There are multiple binaries and a library that will be produced.
The binaries correspond to the files in `./src/bin`.
All are straightforward except for `haploid`, which performs full simplification of the input.

All binaries parse and output smt format, which can be given via a file on the command line, or by pipe-ing the smt2 query into the executable.
By default output is printed, but a file can be specified with `-o`

```
> ./target/bin/haploid benchmarks/examples/example_0.smt2
(declare-const principal_account String)
(declare-const principal_partition Int)
(declare-const principal_prefix Int)
(declare-const principal_region Int)
(declare-const principal_type Int)
(assert (= "111122223333" principal_account))
(assert (= principal_partition 0))
(assert (= principal_prefix 0))
(assert (= principal_region 0))
(assert (= principal_type 1))
(check-sat)
(get-model)

> cat benchmarks/examples/example_1.smt2 | ./target/bin/haploid
(declare-const enumVariable Int)
(assert (= enumVariable 0))
(check-sat)
(get-model)
```


## File Manifest

Each directory contains a README describing the file in more detail

* __benchmarks__: A few example and test inputs to Haploid. Also where the benchmark download script will place benchmarks.
* __scripts__: Any python and bash scripts used for benchmarking.
* __src__: Rust source tree.
