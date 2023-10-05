# Simplify Asserts

The main hub of Haploid.

To use `egg` you need to create a _language_ for it.

Since parsing is done by `smt2parser` and `egg` requires a specific ast format in memory we need to define both a language to use in `egg` and transformers back and forth between these representations.

The main flow in `simplify_asserts` from `mod.rs`:

1. Simplify assignments
    1. Make an EGraph
    2. Take all commands of the form `(assert (= <some> <other>))` and put both `<some>` and `<other>` into the EGraph
    3. Run with expansion and reduction rules for a few iterations
    4. Run with reduction rules until saturation
    5. Extract out the simplest version of each `<some>` and `<other>`
2. Make an EGraph
3. Put in all the simplified assignments and union the pairs of EClasses
4. Put in all other asserts
5. Run with expansion and reduction rules for a few iterations
6. Run with reduction rules and unit propagation until saturation
    1. Track asserted terms
    2. If any term becomes a unit expression union it with the value `true`
7. Determine variable renaming
    1. Track EClass id to variable mapping
    2. Pick one chosen variable for each EClass
    3. Make a mapping from non chosen variables to their representative chosen variable
8. Extract out the simplest version of each asserted term
    1. If the new term has the same cost as the original, use the original
    2. If the new term is `true`, use the simplified version from before using unit propagation
    3. Apply renaming
9. Reconstruct the query
    1. Iterate through the query passing values through until an assert is reached
    2. Inject `(assert (= <a> <b>))` where `<a>` and `<b>` are variable names from renaming, this is needed so we don't make variables become unconstrained
    3. For all asserts use their best value from above
    4. If a contradiction was found while running the EGraph a `Contradiction` will be generated, translate these to `(assert false)`
    5. If the term was extracted as `true` at the end of 8. then don't emit an assert


## File Manifest

* __analysis.rs__: `egg` EGraph analysis for the `EggSmt` language, currently does constant folding.
* __ast_to_recexpr.rs__: Transformer from `smt2parser`'s concrete ast to the `RecExpr<EggSmt>` used by `egg`
* __cost.rs__: A simple cost function for the `EggSmt` language
* __language.rs__: The `EggSmt` language definition
* __mod.rs__: The actual simplifier using these other files
* __recexpr_to_ast.rs__: Transformer from `RecExpr<EggSmt>` used by `egg` to the concrete ast
* __rewrite_rules.rs__: Rewrite rules for `EggSmt`