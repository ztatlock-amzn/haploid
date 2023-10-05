# Src

Haploid is designed to be both a library and binary and can be used either way.

## File Manifest

* __bin__: Directory containing source for generated executables.
* __simplify_asserts__: Directory containing the bulk of the EGraph simplification code.
* __dump_commands.rs__: Printing/file output of a query
* __lib.rs__: The library interface to Haploid
* __lift_assert_or_and.rs__: Single purpose rewrite to perform the rewrite `(and (or same a) (or same b) ...)` goes to `(and same (or a b ...))`
* __parse_input.rs__: Input reader that either takes from a file or standard in and parses it as smt2
* __sort_commands.rs__: Sort a query so that it is in the order configuration, variable declarations, assignment asserts, general asserts, check sat. Within each category also sort alphabetically.
* __split_assert_and__: Single purpose rewrite to perform the rewrite `(assert (and a b c)` goes to `(assert a)(assert b)(assert c)`