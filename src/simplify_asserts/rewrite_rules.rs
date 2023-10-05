use super::language::EggSmt;
use egg::{rewrite, Analysis, Rewrite};

/// Rewrite rules which increase the size of the E-Graph exponentially.
pub fn expansion_rules<A: Analysis<EggSmt>>() -> Vec<Rewrite<EggSmt, A>> {
    vec![
        // Boolean Rules
        // From Theorem 2 page 35 of
        // "Discrete Mathematics: Mathematical Reasoning and Proof with Puzzles, Patterns, and Games"
        // by Douglas E. Ensley and J. Winston Crawley
        rewrite! {"commutative_and";     "(and ?p ?q)"          => "(and ?q ?p)"},
        rewrite! {"commutative_or";      "(or ?p ?q)"           => "(or ?q ?p)"},
        //
        rewrite! {"associative_and";     "(and (and ?p ?q) ?r)" => "(and ?p (and ?q ?r))"},
        rewrite! {"associative_or";      "(or (or ?p ?q) ?r)"   => "(or ?p (or ?q ?r))"},
        //
        rewrite! {"distributive_and_or"; "(and ?p (or ?q ?r))"  => "(or (and ?p ?q) (and ?p ?r))"},
        rewrite! {"distributive_or_and"; "(or ?p (and ?q ?r))"  => "(and (or ?p ?q) (or ?p ?r))"},
        //
        rewrite! {"demorgans_and";       "(not (and ?p ?q))"    => "(or (not ?p) (not ?q))"},
        rewrite! {"demorgans_or";        "(not (or ?p ?q))"     => "(and (not ?p) (not ?q))"},
        //
        // Added Rules
        rewrite! {"implicate";           "(or (not ?a) ?b)"     => "(=> ?a ?b)"},
        rewrite! {"deimplicate";         "(=> ?a ?b)"           => "(or (not ?a) ?b)"},
        rewrite! {"commutative_eq";      "(= ?a ?b)"            => "(= ?b ?a)"},
        rewrite! {"yash_pote";   "(or (and ?a ?b) (and ?a ?c))" => "(and ?a (or ?b ?c))"},
    ]
}

/// Rewrite rules which linearly increase the size of the E-GRaph, or may shrink it.
pub fn reduction_rules<A: Analysis<EggSmt>>() -> Vec<Rewrite<EggSmt, A>> {
    vec![
        // Boolean Rules
        // From Theorem 2 page 35 of
        // "Discrete Mathematics: Mathematical Reasoning and Proof with Puzzles, Patterns, and Games"
        // by Douglas E. Ensley and J. Winston Crawley
        rewrite! {"identity_and";        "(and ?p true)"       => "?p"},
        rewrite! {"identity_or";         "(or ?p false)"       => "?p"},
        //
        rewrite! {"negation_and";        "(and ?p (not ?p))"   => "false"},
        rewrite! {"negation_or";         "(or ?p (not ?p))"    => "true"},
        //
        rewrite! {"double_negative";     "(not (not ?p))"      => "?p"},
        //
        rewrite! {"idempotent_and";      "(and ?p ?p)"         => "?p"},
        rewrite! {"idempotent_or";       "(or ?p ?p)"          => "?p"},
        //
        rewrite! {"universal_bound_and";  "(and ?p false)"     => "false"},
        rewrite! {"universal_bound_or";   "(or ?p true)"       => "true"},
        //
        rewrite! {"absorption_and";      "(and ?p (or ?p ?q))" => "?p"},
        rewrite! {"absorption_or";       "(or ?p (and ?p ?q))" => "?p"},
        //
        rewrite! {"negation_true";       "(not true)"          => "false"},
        rewrite! {"negation_false";      "(not false)"         => "true"},
        //
        // Added rules
        rewrite! {"imply_same";          "(=> ?a (or ?a ?b))"  => "true"},
        rewrite! {"eq_refl";             "(= ?a ?a)"           => "true"},
        rewrite! {"eq_true";             "(= true ?a)"         => "?a"},
        rewrite! {"eq_false";            "(= false ?a)"        => "(not ?a)"},
        rewrite! {"ite_true";            "(ite true ?a ?b)"    => "?a"},
        rewrite! {"ite_false";           "(ite false ?a ?b)"   => "?b"},
        rewrite! {"illusion_of_choice";  "(ite ?a ?b ?b)"      => "?b"},
        // Regex Rewrites
        rewrite! {"re_combine"; "(re.++ (str.to_re ?l) (str.to_re ?r))" => "(str.to_re (str.++ ?l ?r))"},
        rewrite! {"kevin_lotz"; "(str.in_re ?s (re.++ (str.to_re ?p) (re.* re.allchar)))" => "(str.prefixof ?p ?s)"},
        rewrite! {"glob"; "(str.in_re ?s (re.* re.allchar))" => "true"},
    ]
}
