# Fuzz Testing

This is a system built around the [Murxla](https://github.com/murxla/murxla) SMT fuzzer.

We can't quite use Murxla directly in the _online solver_ mode for a few reasons

* Haploid requires that stdin be closed before it begins to do anything, and Murxla expects responses while keeping stdin open
* Haploid does not support some things murxla cannot avoid (`push`, `pop`, etc)
* We want to know if the `smt2parser` failed, Haploid failed, the solver failed, or if Haploid changed the meaning of the query

As such we use Murxla in one shot mode and pass the generated query through a cleanup script.
In one shot mode the query that gets generated is determined by the seed given to Murxla.

The `fuzz-haploid.py` script will generate SMT2 queries and report errors until canceled.
All errors will cause a file to be written out that is named according to the error source.

* `smt2parser` for when the external parser library throws an error
* `haploid` for when Haploid throws an error
* `solver` for when the solver (default cvc5) throws an error
* `haploid_plus_solver` for when passing Haploid's output through the solver throws an error
* `disagreement` for when Haploid caused the query to change meaning

## File Manifest

* __scripts__: Fuzzing scripts
    * __build-murxla.sh__: Simple script to clone and build Murxla. Note: Murxla requires a more modern compiler than the default on AL2, so you will need to run `sudo yum install gcc10.x86_64 gcc10-c++.x86_64` and set cmake's compilers (in bash this is `export CC=gcc10-gcc` and `export CXX=ggg10-g++` before running the build script
    * __clean_fuzzing_query.py__: Script that removes unsupported commands from an SMT2 query, this can change teh meaning of queries and as such is not a safe transform in general. We can use it since we are just looking for bugs.
    * __fuzz-haploid.py__: The driver for fuzzing.
    * __wrapped-cvc5.sh__: A script around `cvc5` that the driver uses. 
    * __wrapped-z3.sh__: A script around `z3` that the driver uses. 