# Regression Tests

These files are used as simple regressions tests for Haploid.
Each file is an SMT query followed by the expected output from Haploid, commended out by `;; EXPECTED: `.
They are made to be used with the `scripts/regression-tester.py` file.

At this point there are still some outputs that do not exactly match what is expected, the output is logically equivalent, but we should keep them as failing until the output is improved.

## File Manifest

* __bugs__: These are files that either exposed an unsoundness in Haploid, or caused a crash. Most are not reduced output from the Murxla fuzzer.
* __constant_folding__: Hand made examples to test that constant folding is sane.
* __small__: Other inputs given as examples.
