# Bin

There are multiple binaries generated.
Most of these are for debugging or hypothesis testing.

## Haploid

The main binary is `haploid` which performs these operations:

1. Parse the input (either given filename or text on standard in)
2. Perform the rewrite `(assert (and a b c)` goes to `(assert a)(assert b)(assert c)` to expose more asserts
3. Perform the rewrite `(assert (and (or same a) (or same b) ...))` goes to `(assert same)(assert (or a b ...))`, which exposes that `same`
4. Sort the commands
5. Use the EGraph simplifier
6. Output the query (either to the file given by `-o` or to stdout)

Setting the environment variable `RUST_LOG` to `debug` will enable a large number of debugging prints.

## File Manifest

* __haploid.rs__: Full simplification and forward solving.
* __lift_assert_or_and.rs__: Just use the rewrite `(and (or same a) (or same b) ...)` goes to `(and same (or a b ...))`
* __round_trip.rs__: Parse the file in, transform it to the `egg` representation, then back, and finally print it. This should not recreate the exact input query, but they should be semantically identical. Differences come from whitespace/comment differences and from n-ary boolean operations. All adjacent boolean `and` and `or` operation will be joined.
* __sort.rs__: Just sort the query commands.
* __split.rs__: Just use the rewrite `(assert (and a b c)` goes to `(assert a)(assert b)(assert c)`
* __split_and_sort.rs__: Perform both of the above