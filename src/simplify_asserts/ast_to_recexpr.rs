use super::language::{self, WrappedAttributeValue};
use crate::{match_or_and, simplify_asserts::language::EggSmt};
use egg::{Id, RecExpr};
use num::BigUint;
use smt2parser::concrete as ast;

/// Converts a Term in the parser's concrete ast into a RecExpr in the EggSmt language
pub fn ast_to_recexpr(term: &ast::Term) -> egg::RecExpr<EggSmt> {
    let mut nodes = vec![];
    term_to_nodes(term, &mut nodes);
    RecExpr::from(nodes)
}

/// Add the given term to the nodes representation and return the Id of the new element.
/// Each element in nodes is a language element in EggSmt, if that element needs to reference
///   other elements (like 'and', which has 2 arguments), then those are held as Ids.
/// These Ids are simply indices into the nodes Vec.
/// There is a requirement that an element can only contain Ids lower than itself.
/// As such, when transforming, we must recurse before forming the current node, that way all
///   referenced IDs will already have a place in the nodes Vec.
fn term_to_nodes(term: &ast::Term, nodes: &mut Vec<EggSmt>) -> Id {
    match match_or_and(term) {
        Some((common_term, or_term)) => {
            return term_to_nodes(
                &ast::Term::Application {
                    qual_identifier: ast::QualIdentifier::Simple {
                        identifier: ast::Identifier::Simple {
                            symbol: ast::Symbol("and".to_string()),
                        },
                    },
                    arguments: vec![common_term.clone(), or_term],
                },
                nodes,
            );
        }
        None => (),
    };
    match term {
        ast::Term::Constant(c) => constant_to_nodes(c, nodes),
        ast::Term::QualIdentifier(qi) => qualidentifier_to_nodes(qi, nodes),
        ast::Term::Application {
            qual_identifier,
            arguments,
        } => {
            let arg_ids: Vec<Id> = arguments.iter().map(|a| term_to_nodes(a, nodes)).collect();

            let item = match qual_identifier {
                // EggSmt differentiates between normal application forms, and ones using an indexed identifier as the called function
                ast::QualIdentifier::Simple { identifier } => match identifier {
                    // Since EggSmt has specific types for some applications we need to identify those here
                    // The following line is noted in documentation, if it is no longer line 53 please update
                    // documentation/adding_an_smt_function.md
                    ast::Identifier::Simple { symbol } => match symbol.0.as_str() {
                        // Boolean Operators
                        "and" => match arg_ids.len() {
                            1 => nodes[usize::from(arg_ids[0])].clone(), // just grab out what is inside and forget the `and`
                            _ => nary_to_binary_left(arg_ids, nodes, EggSmt::And),
                        },
                        "or" => match arg_ids.len() {
                            1 => nodes[usize::from(arg_ids[0])].clone(), // same for `or`
                            _ => nary_to_binary_left(arg_ids, nodes, EggSmt::Or),
                        },
                        "=>" => nary_to_binary_right(arg_ids, nodes, EggSmt::Implies),
                        "not" => EggSmt::Not(arg_ids.try_into().unwrap()),
                        "ite" => EggSmt::IfThenElse(arg_ids.try_into().unwrap()),

                        // String Operators
                        "str.++" => nary_to_binary_left(arg_ids, nodes, EggSmt::StrConcat),
                        "str.contains" => EggSmt::StrContains(arg_ids.try_into().unwrap()),
                        "str.in_re" => EggSmt::StrInRe(arg_ids.try_into().unwrap()),
                        "str.len" => EggSmt::StrLen(arg_ids.try_into().unwrap()),
                        "str.prefixof" => EggSmt::StrPrefixof(arg_ids.try_into().unwrap()),
                        "str.substr" => EggSmt::StrSubstr(arg_ids.try_into().unwrap()),
                        "str.suffixof" => EggSmt::StrSuffixof(arg_ids.try_into().unwrap()),
                        "str.to_re" => EggSmt::StrToRe(arg_ids.try_into().unwrap()),

                        // Regex Operators
                        "re.*" => EggSmt::ReStar(arg_ids.try_into().unwrap()),
                        "re.++" => nary_to_binary_left(arg_ids, nodes, EggSmt::ReConcat),
                        "re.union" => nary_to_binary_left(arg_ids, nodes, EggSmt::ReUnion),

                        // Math Operators
                        "+" => nary_to_binary_left(arg_ids, nodes, EggSmt::Add),
                        "-" => match arg_ids.len() {
                            1 => EggSmt::Neg(arg_ids.try_into().unwrap()),
                            _ => nary_to_binary_left(arg_ids, nodes, EggSmt::Sub),
                        },
                        "*" => nary_to_binary_left(arg_ids, nodes, EggSmt::Mul),
                        "/" => match arg_ids.len() {
                            1 => {
                                let one = EggSmt::Numeral(BigUint::from(1_u32));
                                nodes.push(one);
                                let one_id = Id::from(nodes.len() - 1);
                                EggSmt::Div([one_id, arg_ids[0]])
                            }
                            _ => nary_to_binary_left(arg_ids, nodes, EggSmt::Div),
                        },
                        "div" => match arg_ids.len() {
                            1 => {
                                let one = EggSmt::Numeral(BigUint::from(1_u32));
                                nodes.push(one);
                                let one_id = Id::from(nodes.len() - 1);
                                EggSmt::IntDiv([one_id, arg_ids[0]])
                            }
                            _ => nary_to_binary_left(arg_ids, nodes, EggSmt::IntDiv),
                        },

                        // Comparators
                        "=" => nary_to_binary_chain(arg_ids, nodes, EggSmt::Equal),
                        "<" => nary_to_binary_chain(arg_ids, nodes, EggSmt::LessThan),
                        "<=" => nary_to_binary_chain(arg_ids, nodes, EggSmt::LessThanEqual),
                        ">" => nary_to_binary_chain(arg_ids, nodes, EggSmt::GreaterThan),
                        ">=" => nary_to_binary_chain(arg_ids, nodes, EggSmt::GreaterThanEqual),

                        // Binary Operators
                        "bvand" => nary_to_binary_left(arg_ids, nodes, EggSmt::BinaryAnd),

                        _ => EggSmt::Application(egg::Symbol::from(&symbol.0), arg_ids),
                    },
                    ast::Identifier::Indexed {
                        symbol: _symbol,
                        indices: _indices,
                    } => {
                        let mut packed = vec![identifier_to_nodes(identifier, nodes)];
                        packed.extend(arg_ids);
                        EggSmt::IdentifierApplication(packed)
                    }
                },
                ast::QualIdentifier::Sorted {
                    identifier: _identifier,
                    sort: _sort,
                } => {
                    todo!("Sorted identifiers not yet supported");
                }
            };

            nodes.push(item);
            Id::from(nodes.len() - 1)
        }
        ast::Term::Let { var_bindings, term } => {
            // Reminder: a let binding n symbols is encoded as 2*n+1 items. The first 2*n are the bindings and the last one is the body of the let
            let mut inner = Vec::with_capacity(2 * var_bindings.len() + 1);
            for (sym, trm) in var_bindings.iter() {
                inner.push(symbol_to_nodes(sym, nodes));
                inner.push(term_to_nodes(trm, nodes));
            }
            inner.push(term_to_nodes(term, nodes));
            nodes.push(EggSmt::Let(inner));
            Id::from(nodes.len() - 1)
        }
        ast::Term::Forall { vars, term } => {
            // Reminder: forall has a similar encoding to let
            let mut inner = Vec::with_capacity(2 * vars.len() + 1);
            for (sym, srt) in vars.iter() {
                inner.push(symbol_to_nodes(sym, nodes));
                inner.push(sort_to_nodes(srt, nodes));
            }
            inner.push(term_to_nodes(term, nodes));
            nodes.push(EggSmt::Forall(inner));
            Id::from(nodes.len() - 1)
        }
        ast::Term::Exists { vars, term } => {
            // Reminder: exists has a similar encoding to let
            let mut inner = Vec::with_capacity(2 * vars.len() + 1);
            for (sym, srt) in vars.iter() {
                inner.push(symbol_to_nodes(sym, nodes));
                inner.push(sort_to_nodes(srt, nodes));
            }
            inner.push(term_to_nodes(term, nodes));
            nodes.push(EggSmt::Exists(inner));
            Id::from(nodes.len() - 1)
        }
        ast::Term::Match {
            term: _term,
            cases: _cases,
        } => {
            todo!("Match not supported")
        }
        ast::Term::Attributes { term, attributes } => {
            // Reminder: a ! holding n attributes is encoded as 2*n+1 items. The first item is the body, and the rest 2*n items are the attribute name, value pairs
            let mut inner = Vec::with_capacity(2 * attributes.len() + 1);
            inner.push(term_to_nodes(term, nodes));
            for (kwd, val) in attributes.iter() {
                inner.push(keyword_to_nodes(kwd, nodes));
                inner.push(attributevalue_to_nodes(val, nodes));
            }
            nodes.push(EggSmt::Attribute(inner));
            Id::from(nodes.len() - 1)
        }
    }
}

/// Converts `(<op> a b c ...)` into `(<op> a (<op> b (<op> c ...)))`
/// creating a right associated version of the expression
fn nary_to_binary_right(
    arg_ids: Vec<Id>,
    nodes: &mut Vec<EggSmt>,
    op: fn([Id; 2]) -> EggSmt,
) -> EggSmt {
    let mut reduced_arg_ids = arg_ids;
    while reduced_arg_ids.len() > 2 {
        let right = reduced_arg_ids.pop().unwrap();
        let left = reduced_arg_ids.pop().unwrap();
        let new = op([left, right]);
        nodes.push(new);
        let id = Id::from(nodes.len() - 1);
        reduced_arg_ids.push(id);
    }
    op(reduced_arg_ids.try_into().unwrap())
}

/// Converts `(<op> a b c ...)` into `(<op> (<op> (<op> a b) c) ...)`
/// creating a left associated version of the expression
fn nary_to_binary_left(
    arg_ids: Vec<Id>,
    nodes: &mut Vec<EggSmt>,
    op: fn([Id; 2]) -> EggSmt,
) -> EggSmt {
    let mut reduced_arg_ids = arg_ids;
    reduced_arg_ids.reverse();
    while reduced_arg_ids.len() > 2 {
        let left = reduced_arg_ids.pop().unwrap();
        let right = reduced_arg_ids.pop().unwrap();
        let new = op([left, right]);
        nodes.push(new);
        let id = Id::from(nodes.len() - 1);
        reduced_arg_ids.push(id);
    }
    reduced_arg_ids.reverse();
    op(reduced_arg_ids.try_into().unwrap())
}

/// Converts nary comparisons to binary pairs
/// For example `(< a b c)` into `(and (< a b) (< b c))`
fn nary_to_binary_chain(
    arg_ids: Vec<Id>,
    nodes: &mut Vec<EggSmt>,
    op: fn([Id; 2]) -> EggSmt,
) -> EggSmt {
    if arg_ids.len() == 2 {
        op([arg_ids[0], arg_ids[1]])
    } else {
        let reduced_args = arg_ids
            .windows(2)
            .map(|w| {
                let comp = op([w[0], w[1]]);
                nodes.push(comp);
                Id::from(nodes.len() - 1)
            })
            .collect();
        nary_to_binary_left(reduced_args, nodes, EggSmt::And)
    }
}

fn constant_to_nodes(cst: &ast::Constant, nodes: &mut Vec<EggSmt>) -> Id {
    let item = match cst {
        ast::Constant::Numeral(n) => EggSmt::Numeral(n.clone()),
        ast::Constant::Decimal(d) => EggSmt::Decimal(d.clone()),
        ast::Constant::Hexadecimal(h) => {
            EggSmt::Hexadecimal(language::WrappedHexadecimal { hex: h.clone() })
        }
        ast::Constant::Binary(b) => EggSmt::Binary(language::WrappedBinary { bin: b.clone() }),
        ast::Constant::String(s) => EggSmt::String(s.clone()),
    };
    nodes.push(item);
    Id::from(nodes.len() - 1)
}

fn qualidentifier_to_nodes(qi: &ast::QualIdentifier, nodes: &mut Vec<EggSmt>) -> Id {
    match qi {
        ast::QualIdentifier::Simple { identifier } => identifier_to_nodes(identifier, nodes),
        ast::QualIdentifier::Sorted { identifier, sort } => {
            let iden = identifier_to_nodes(identifier, nodes);
            let srt = sort_to_nodes(sort, nodes);
            let item = EggSmt::Application(egg::Symbol::from("as"), vec![iden, srt]);
            nodes.push(item);
            Id::from(nodes.len() - 1)
        }
    }
}

fn identifier_to_nodes(iden: &ast::Identifier, nodes: &mut Vec<EggSmt>) -> Id {
    let item = match iden {
        ast::Identifier::Simple { symbol } => match symbol.0.as_str() {
            "true" => EggSmt::Boolean(true),
            "false" => EggSmt::Boolean(false),
            sym => EggSmt::Symbol(egg::Symbol::from(sym)),
        },
        ast::Identifier::Indexed { symbol, indices } => {
            let mut inner = Vec::with_capacity(1 + indices.len());
            let sym_id = symbol_to_nodes(symbol, nodes);
            inner.push(sym_id);
            inner.extend(indices.iter().map(|i| index_to_nodes(i, nodes)));
            EggSmt::Identifier(inner)
        }
    };
    nodes.push(item);
    Id::from(nodes.len() - 1)
}

fn sort_to_nodes(srt: &ast::Sort, nodes: &mut Vec<EggSmt>) -> Id {
    let item = match srt {
        ast::Sort::Simple { identifier } => return identifier_to_nodes(identifier, nodes),
        ast::Sort::Parameterized {
            identifier,
            parameters,
        } => {
            let prm_ids = parameters.iter().map(|p| sort_to_nodes(p, nodes)).collect();
            EggSmt::Application(egg::Symbol::from(identifier.to_string()), prm_ids)
        }
    };
    nodes.push(item);
    Id::from(nodes.len() - 1)
}

fn symbol_to_nodes(symbol: &ast::Symbol, nodes: &mut Vec<EggSmt>) -> Id {
    nodes.push(EggSmt::Symbol(egg::Symbol::from(&symbol.0)));
    Id::from(nodes.len() - 1)
}

fn keyword_to_nodes(keyword: &ast::Keyword, nodes: &mut Vec<EggSmt>) -> Id {
    nodes.push(EggSmt::Symbol(egg::Symbol::from(keyword.0.clone())));
    Id::from(nodes.len() - 1)
}

fn attributevalue_to_nodes(val: &ast::AttributeValue, nodes: &mut Vec<EggSmt>) -> Id {
    nodes.push(EggSmt::AttributeValue(WrappedAttributeValue {
        val: val.clone(),
    }));
    Id::from(nodes.len() - 1)
}

fn index_to_nodes(idx: &smt2parser::visitors::Index, nodes: &mut Vec<EggSmt>) -> Id {
    let item = match idx {
        smt2parser::visitors::Index::Numeral(n) => EggSmt::Numeral(n.clone()),
        smt2parser::visitors::Index::Symbol(symbol) => match symbol.0.as_str() {
            "true" => EggSmt::Boolean(true),
            "false" => EggSmt::Boolean(false),
            sym => EggSmt::Symbol(egg::Symbol::from(sym)),
        },
    };
    nodes.push(item);
    Id::from(nodes.len() - 1)
}
