# Adding an SMT Function

To add a new SMT function you will need to modify 4 files, with an optional file for any rewrites.
These are all in `src/simplify_asserts`, the following sections give the short version of what to change as well as a longer explanation on the purpose of the file.
I will go through the modifications required to add the fictional `foo` function to Haploid.
This `foo` function is binary, though it can be written with any number of arguments which are interpreted as being left associative.

## `language.rs`

Within the `pub enum EggSmt` starting on line 16 add the line `"foo" = Foo([Id; 2]),`.
This declares `Foo` as a variant in the language which takes in two other expressions as arguments (`[Id; 2]`), and defines that it will be written as an s-expression starting with "foo".

The purpose of this file is to define the language that the EGraph will understand.
[Egg](https://docs.rs/egg/latest/egg/) uses an ast form called a `RecExpr`, so we need to make a language that can be used in it.
This language is made to match the features we want to use and pass through those we don't want.
Since this is connecting the `smt2parser` concrete ast to the `Egg::RecExpr` there are a few wrapping structs used for types that `smt2parser` does not expose.
In addition there is the `Contradiction` ast node that is used as a poison value for when contradictions are found.
Some terms in smt, such as `forall` can't be written in the language form used, and so are packed when found.
These are the variants near the bottom of the macro which contain `Vec<Id>`, with comments explaining how they are formed.


## `ast_to_recexpr.rs`

Within the match formed by the line `ast::Identifier::Simple { symbol } => match symbol.0.as_str() {` on line 53 add the line `"foo" => nary_to_binary_left(arg_ids, nodes, EggSmt::Foo),`.
This picks out any `(foo ...)` terms in the `smt2parser` ast and builds a `RecExpr` form with our `Foo` variant that is both binary and left associated.
In place of this function there could also be `nary_to_binary_right` for right associated functions, `nary_to_binary_chain` for chained comparisons, or simply `EggSmt::Foo(arg_ids.try_into().unwrap())` if the function can't be present in SMT with any number of arguments.

As stated, we need to transform the `smt2parser::concrete` ast into a `egg::RecExpr<EggSmt>` ast, which I will call ast and recexpr.
A recexpr is really just a list of `EggSmt` variants called nodes
In `language.rs` most of the forms use an `Id` type, this is used as an index in the nodes where that other language node is.
For instance, the expression `(and a true)` will become a nodes list similar to `[Symbol("a"),Boolean(true), And([Id(0), Id(1)])]`.
For a nodes list to be valid all `Id`s used must be for indicies before that item in the list.
As such, to build a recepr from an ast we do a depth first traversal.
No attempt is made to deduplicate nodes, since that will be done on insertion into the EGraph.


## `recexpr_to_ast.rs`

Withing the match formed by line 24, `match &nodes[usize::from(idx)] {`, add the line `EggSmt::Foo(args) => regroup_nary_left(nodes, args, "and", make_extractor!(EggSmt::Foo)),`.
This will allow transformation back into the `smt2parser` ast, and will regroup nearby `foo` expressions.
There also exists a `right` variant of the function.
If no binary conversion was used then the `regroup...` call should be `handle_application(nodes, "foo", args.as_ref()),`.

Transformation from ast to recexpr is a bit easier, for correctness sake there is no need to recombine binary operators, but it is a nice thing to do if you are going to be reading the output.


## `analysis.rs`

Constant propagation is done in this file.
If you don't want to do constant propagation then within the match on line 28 starting with `match enode {` just add `EggSmt::Foo(_) => None`.
Now `foo` is part of Haploid (though I would heavily recommend adding constant propagation and maybe some rewrite rules)!

To add constant evaluation instead add the line `EggSmt::Foo([a, b]) => const_fold_foo(id_to_data(a), id_to_data(b)),`.
This extracts out the arguments of foo, then gets their associated data, and calls a function we will need to write.
At the file level we will need to make our `const_fold_foo` function.
It will take the following form:

```
fn const_fold_foo(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::TYPE(a)), Some(Constant::TYPE(b))) => Some(Constant::TYPE(...))
        _ => None,
    }
}
```

Of course the `TYPE` and `...` will need to be filled in depending on what `foo` does.


An `Analysis` adds some data to each EClass that you can control and update as the EGraph is running.
Our analysis attaches a `Option<Constant>` type, which we use to represent constant values.
This option is `None` when there is no constant and `Some` when a constant value is known.
As such the functions that handle individual functions match on whether the inputs are constant, and what type those inputs are.



## `rewrite_rules.rs`

This file is split into two large `vec!` macro calls.
The first is where potentially self enabling rewrites go, and the second is where rewrites that only reduce the expressions go.
All rewrites are made with `rewrite!{"name"; "<from-pattern>" => "<to-pattern>"}`.
The name must be unique.
Examining the existing patterns may be useful.
