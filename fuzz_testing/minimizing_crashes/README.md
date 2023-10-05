# Minimizing Crashes

These are the inputs that were found to cause an error with cvc5.

All of them are queries that run under cvc5 without issue, but when simplified by Haploid an error arrises.

Most of these files are to track how the error causing input was found.
The results are in the `possible_bugs` directory.

## File Manifest

* __source__: Fuzzer-generated queries
* __haploided__: Simplified queries that cause errors
* __minimized__: Reduced error causing queries
* __possible_bugs__: Transforming the reduced queries into examples
