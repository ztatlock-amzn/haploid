# Scripts

This is the main group of runscripts for testing or benchmarking Haploid.

## File Manifest

* __can-haploid-solve.py__: Benchmark runner that only runs Haploid to see if it solved the query.
* __clean_query.py__: A query transformer that tries to remove things that might interfere with benchmarking, such as setting `rlimit` or containing expressions Haploid doesn't support (such as `reset` or `pop`)
* __find-unique-files.py__: Makes a list of all smt2 files in a directory, deduplicated by hash.
* Translators for smt2 to allow benchmarks to be ran by the named solver
    * __handle_cvc4.py__
    * __handle_cvc5.py__
    * __handle_z3_4_8_17.py__
    * __handle_z3_4_8_5.py__
