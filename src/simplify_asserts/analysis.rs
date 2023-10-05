use super::language::{EggSmt, WrappedBinary, WrappedHexadecimal};
use crate::simplify_asserts::language;
use egg::{merge_option, Analysis, DidMerge, Id};
use log::debug;
use num::{bigint::Sign, BigInt, Signed, ToPrimitive, Zero};
use unicode_segmentation::UnicodeSegmentation;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Constant {
    Numeral(BigInt),
    Decimal(smt2parser::Decimal),
    Hexadecimal(smt2parser::Hexadecimal),
    Binary(smt2parser::Binary),
    String(String),
    Boolean(bool),
    Contradiction(language::Contradiction),
}

#[derive(Default)]
pub struct Eval;
impl Analysis<EggSmt> for Eval {
    type Data = Option<Constant>;

    fn make(egraph: &egg::EGraph<EggSmt, Self>, enode: &EggSmt) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref();
        // The following line is noted in documentation, if it is no longer line 28 please update
        // documentation/adding_an_smt_function.md
        match enode {
            // Constant Atoms
            EggSmt::Numeral(n) => Some(Constant::Numeral(BigInt::from_biguint(
                Sign::Plus,
                n.clone(),
            ))),
            EggSmt::Decimal(d) => Some(Constant::Decimal(d.clone())),
            EggSmt::Hexadecimal(h) => Some(Constant::Hexadecimal((*h.hex).to_vec())),
            EggSmt::Binary(b) => Some(Constant::Binary((*b.bin).to_vec())),
            EggSmt::Boolean(b) => Some(Constant::Boolean(*b)),
            EggSmt::String(s) => Some(Constant::String(s.clone())),

            // Non-Constant Atom
            EggSmt::Symbol(_) => None,

            // Boolean Operators
            EggSmt::And([a, b]) => const_fold_and(x(a), x(b)),
            EggSmt::Or([a, b]) => const_fold_or(x(a), x(b)),
            EggSmt::Implies([a, b]) => const_fold_implies(x(a), x(b)),
            EggSmt::Not([a]) => const_fold_not(x(a)),
            EggSmt::IfThenElse(_) => None,

            // String Operators
            EggSmt::StrConcat([a, b]) => const_fold_str_concat(x(a), x(b)),
            EggSmt::StrContains([a, b]) => const_fold_str_contains(x(a), x(b)),
            EggSmt::StrInRe([_a, _b]) => None, // TODO: constant fold str.in_re
            EggSmt::StrLen([a]) => const_fold_str_len(x(a)),
            EggSmt::StrPrefixof([a, b]) => const_fold_str_prefixof(x(a), x(b)),
            EggSmt::StrSubstr([a, b, c]) => const_fold_str_substr(x(a), x(b), x(c)),
            EggSmt::StrSuffixof([a, b]) => const_fold_str_suffixof(x(a), x(b)),
            EggSmt::StrToRe([_a]) => None, // TODO: constant fold str.to_re

            // Regex Operators
            EggSmt::ReStar([_a]) => None, // TODO: constant fold re.*
            EggSmt::ReConcat([_a, _b]) => None, // TODO: constant fold re.++
            EggSmt::ReUnion([_a, _b]) => None, // TODO: constant fold re.union

            // Math Operators
            EggSmt::Add([a, b]) => const_fold_add(x(a), x(b)),
            EggSmt::Sub([a, b]) => const_fold_sub(x(a), x(b)),
            EggSmt::Mul([a, b]) => const_fold_mul(x(a), x(b)),
            EggSmt::Div([_a, _b]) => None, // TODO: constant fold Real division
            EggSmt::IntDiv([a, b]) => const_fold_int_div(x(a), x(b)),
            EggSmt::Neg([a]) => const_fold_neg(x(a)),

            // Comparators
            EggSmt::Equal([a, b]) => const_fold_equal(x(a), x(b)),
            EggSmt::LessThan([a, b]) => const_fold_less_than(x(a), x(b)),
            EggSmt::LessThanEqual([a, b]) => const_fold_less_than_equal(x(a), x(b)),
            EggSmt::GreaterThan([a, b]) => const_fold_greater_than(x(a), x(b)),
            EggSmt::GreaterThanEqual([a, b]) => const_fold_greater_than_equal(x(a), x(b)),

            // Binary Operators
            EggSmt::BinaryAnd([a, b]) => const_fold_binary_and(x(a), x(b)),

            // Other
            EggSmt::Attribute(packed) => egraph[packed[0]].data.clone(),
            EggSmt::AttributeValue(_) => None,
            EggSmt::Forall(_) => None,
            EggSmt::Let(_) => None,
            EggSmt::Exists(_) => None,
            EggSmt::Identifier(_) => None,
            EggSmt::IdentifierApplication(_) => None,
            EggSmt::Application(_, _) => None,

            // Contradiction
            EggSmt::Contradiction(_) => None,
        }
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            if *a != b {
                debug!(
                    "Merged different values: a == b, but\n  a = {:?}\n  b = {:?}\n",
                    *a, b
                );
                *a = Constant::Contradiction(language::Contradiction {
                    name: "Made by analysis.rs".to_string(),
                });
                DidMerge(true, false)
            } else {
                DidMerge(false, false)
            }
        })
    }

    fn modify(egraph: &mut egg::EGraph<EggSmt, Self>, id: Id) {
        let class = egraph[id].clone();
        if let Some(c) = class.data {
            let enode = match c {
                Constant::Boolean(b) => EggSmt::Boolean(b),
                Constant::Numeral(n) => match n.sign() {
                    Sign::Plus => EggSmt::Numeral(n.to_biguint().unwrap()),
                    Sign::NoSign => EggSmt::Numeral(n.to_biguint().unwrap()),
                    Sign::Minus => {
                        let inner = EggSmt::Numeral((-n).to_biguint().unwrap());
                        let id = egraph.add(inner);
                        EggSmt::Neg([id])
                    }
                },
                Constant::Decimal(d) => EggSmt::Decimal(d),
                Constant::Hexadecimal(h) => EggSmt::Hexadecimal(WrappedHexadecimal { hex: h }),
                Constant::Binary(b) => EggSmt::Binary(WrappedBinary { bin: b }),
                Constant::String(s) => EggSmt::String(s),
                Constant::Contradiction(c) => EggSmt::Contradiction(c),
            };
            let added = egraph.add(enode);
            egraph.union(id, added);

            // Will this delete variables?
            // Make sure there is always at least one enode
            // Do we need to do anything for proofs?
            //egraph[id].nodes.retain(|n| n.is_leaf());
        }
    }
}

// +-------------------------------------------------------------------------+
// | Boolean Operators                                                       |
// +-------------------------------------------------------------------------+
fn const_fold_and(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Boolean(a)), Some(Constant::Boolean(b))) => {
            Some(Constant::Boolean(*a && *b))
        }
        _ => None,
    }
}

fn const_fold_or(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Boolean(a)), Some(Constant::Boolean(b))) => {
            Some(Constant::Boolean(*a || *b))
        }
        _ => None,
    }
}

fn const_fold_implies(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Boolean(a)), Some(Constant::Boolean(b))) => {
            Some(Constant::Boolean((!*a) || *b))
        }
        _ => None,
    }
}

fn const_fold_not(a: Option<&Constant>) -> Option<Constant> {
    match a {
        Some(Constant::Boolean(a)) => Some(Constant::Boolean(!*a)),
        _ => None,
    }
}

// +-------------------------------------------------------------------------+
// | String Operators                                                        |
// +-------------------------------------------------------------------------+

/// String concatenation
///   ⟦str.++⟧ is the word concatenation function.
fn const_fold_str_concat(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::String(l)), Some(Constant::String(r))) => {
            Some(Constant::String(format!("{}{}", l, r)))
        }
        _ => None,
    }
}

/// First string contains second one
/// (str.contains s t) iff s contains t.
fn const_fold_str_contains(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::String(s)), Some(Constant::String(t))) => {
            Some(Constant::Boolean(s.contains(t)))
        }
        _ => None,
    }
}

/// String length
///   ⟦str.len⟧(w) is the number of characters (elements of UC) in w,
///   denoted below as |w|.
///
///   Note: ⟦str.len⟧(w) is **not** the number of bytes used by some Unicode
///         encoding, such as UTF-8 – that number can be greater than the number
///         of characters.
///
///   Note: ⟦str.len(""\u1234"")⟧  is 1 since every escape sequence denotes
///         a single character.
fn const_fold_str_len(a: Option<&Constant>) -> Option<Constant> {
    match a {
        // TODO: Handle weird character encoding things to match SMT spec
        // Do we need to process the character escape codes or has the smt2parser done that for us?
        //
        // From https://stackoverflow.com/questions/46290655/get-the-string-length-in-characters-in-rust
        // * .len()                   returns number of bytes
        // * .chars().count()         returns the number of unicode scalar values
        // * .graphemes(true).count() returns the number of grapheme clusters
        Some(Constant::String(w)) => {
            Some(Constant::Numeral(BigInt::from(w.graphemes(true).count())))
        }
        _ => None,
    }
}

/// First string is a prefix of second one.
///   (str.prefixof s t) is true iff s is a prefix of t.
///
///   ⟦str.prefixof⟧(w₁, w) = true  iff  w = w₁w₂ for some word w₂
fn const_fold_str_prefixof(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::String(s)), Some(Constant::String(t))) => {
            Some(Constant::Boolean(t.starts_with(s)))
        }
        _ => None,
    }
}

/// Substring
///   (str.substr s i n) evaluates to the longest (unscattered) substring
///   of s of length at most n starting at position i.
///   It evaluates to the empty string if n is negative or i is not in
///   the interval [0,l-1] where l is the length of s.
///
///   - ⟦str.substr⟧(w, m, n) is the unique word w₂ such that
///     for some words w₁ and w₃
///     - w = w₁w₂w₃
///     - |w₁| = m
///     - |w₂| = min(n, |w| - m)
///                                    if 0 <= m < |w| and 0 < n
///   - ⟦str.substr⟧(w, m, n) = ε      otherwise
///
///   Note: The second part of the definition makes ⟦str.substr⟧ a total function.
fn const_fold_str_substr(
    a: Option<&Constant>,
    b: Option<&Constant>,
    c: Option<&Constant>,
) -> Option<Constant> {
    match (a, b, c) {
        (Some(Constant::String(w)), Some(Constant::Numeral(m)), Some(Constant::Numeral(n))) => {
            // Make sure this length function matches const_fold_str_len
            let l = w.graphemes(true).count();
            if n.is_negative() || m.is_negative() || m > &BigInt::from(l - 1) {
                Some(Constant::String("".to_string()))
            } else {
                let word = w.graphemes(true);
                let after_m = word.skip(m.to_usize().unwrap());
                let w_2 = after_m.take(n.to_usize().unwrap());
                Some(Constant::String(w_2.collect()))
            }
        }
        _ => None,
    }
}

/// First string is a suffix of second one.
///   (str.suffixof s t) is true iff s is a suffix of t.
///
///   ⟦str.suffixof⟧(w₂, w) = true  iff  w = w₁w₂ for some word w₁
fn const_fold_str_suffixof(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::String(s)), Some(Constant::String(t))) => {
            Some(Constant::Boolean(t.starts_with(s)))
        }
        _ => None,
    }
}

// +-------------------------------------------------------------------------+
// | Math Operators                                                          |
// +-------------------------------------------------------------------------+
fn const_fold_add(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => Some(Constant::Numeral(a + b)),
        _ => None,
    }
}

fn const_fold_sub(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => Some(Constant::Numeral(a - b)),
        _ => None,
    }
}

fn const_fold_mul(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => Some(Constant::Numeral(a * b)),
        _ => None,
    }
}

fn const_fold_int_div(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        // TODO: Add behavior for non-exact division (e.g. (div 10 3))
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => {
            if *b == BigInt::zero() {
                None
            } else if a % b == BigInt::zero() {
                Some(Constant::Numeral(a / b))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn const_fold_neg(a: Option<&Constant>) -> Option<Constant> {
    match a {
        Some(Constant::Numeral(a)) => Some(Constant::Numeral(-a)),
        _ => None,
    }
}

// +-------------------------------------------------------------------------+
// | Comparators                                                             |
// +-------------------------------------------------------------------------+
fn const_fold_equal(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(a), Some(b)) => Some(Constant::Boolean(*a == *b)),
        _ => None,
    }
}

fn const_fold_less_than(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => Some(Constant::Boolean(a < b)),
        _ => None,
    }
}

fn const_fold_less_than_equal(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => Some(Constant::Boolean(a <= b)),
        _ => None,
    }
}

fn const_fold_greater_than(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => Some(Constant::Boolean(a > b)),
        _ => None,
    }
}

fn const_fold_greater_than_equal(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Numeral(a)), Some(Constant::Numeral(b))) => Some(Constant::Boolean(a >= b)),
        _ => None,
    }
}

// +-------------------------------------------------------------------------+
// | Binary Operators                                                        |
// +-------------------------------------------------------------------------+
fn const_fold_binary_and(a: Option<&Constant>, b: Option<&Constant>) -> Option<Constant> {
    match (a, b) {
        (Some(Constant::Binary(a)), Some(Constant::Binary(b))) => Some(Constant::Binary(
            a.iter()
                .zip(b.iter())
                .map(|bits| *bits.0 && *bits.1)
                .collect(),
        )),
        (Some(Constant::Hexadecimal(a)), Some(Constant::Hexadecimal(b))) => {
            Some(Constant::Hexadecimal(
                a.iter()
                    .zip(b.iter())
                    .map(|bytes| *bytes.0 & *bytes.1)
                    .collect(),
            ))
        }
        _ => None,
    }
}

// +-------------------------------------------------------------------------+
// | Other                                                                   |
// +-------------------------------------------------------------------------+
