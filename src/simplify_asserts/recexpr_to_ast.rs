use super::language::EggSmt;
use egg::Id;
use smt2parser::concrete as ast;

macro_rules! make_extractor {
    ( $e:path ) => {
        |es| match es {
            $e(args) => Some(args),
            _ => None,
        }
    };
}

/// Converts a RecExpr in the EggSmt language to a Term in the parser's concrete ast
pub fn recexpr_to_ast(rec: &egg::RecExpr<EggSmt>) -> ast::Term {
    let nodes = rec.as_ref();
    handle_term(nodes, Id::from(nodes.len() - 1))
}

/// The representation of nodes is discussed in ast_to_recexpr.rs
fn handle_term(nodes: &[EggSmt], idx: Id) -> ast::Term {
    // The following line is noted in documentation, if it is no longer line 24 please update
    // documentation/adding_an_smt_function.md
    match &nodes[usize::from(idx)] {
        // Atoms
        EggSmt::Numeral(n) => ast::Term::Constant(ast::Constant::Numeral(n.clone())),
        EggSmt::Decimal(d) => ast::Term::Constant(ast::Constant::Decimal(d.clone())),
        EggSmt::Hexadecimal(h) => ast::Term::Constant(ast::Constant::Hexadecimal(h.hex.clone())),
        EggSmt::Binary(b) => ast::Term::Constant(ast::Constant::Binary(b.bin.clone())),
        EggSmt::Boolean(b) => handle_boolean(*b),
        EggSmt::String(s) => ast::Term::Constant(ast::Constant::String(s.clone())),
        EggSmt::Symbol(sym) => ast::Term::QualIdentifier(ast::QualIdentifier::Simple {
            identifier: ast::Identifier::Simple {
                symbol: ast::Symbol(sym.to_string()),
            },
        }),

        // Boolean Operators
        EggSmt::And(args) => regroup_nary_left(nodes, args, "and", make_extractor!(EggSmt::And)),
        EggSmt::Or(args) => regroup_nary_left(nodes, args, "or", make_extractor!(EggSmt::Or)),
        EggSmt::Implies(args) => {
            regroup_nary_right(nodes, args, "=>", make_extractor!(EggSmt::Implies))
        }
        EggSmt::Not(arg) => handle_application(nodes, "not", arg.as_ref()),
        EggSmt::IfThenElse(args) => handle_application(nodes, "ite", args.as_ref()),

        // String Operators
        EggSmt::StrConcat(args) => {
            regroup_nary_left(nodes, args, "str.++", make_extractor!(EggSmt::StrConcat))
        }
        EggSmt::StrContains(args) => handle_application(nodes, "str.contains", args.as_ref()),
        EggSmt::StrInRe(args) => handle_application(nodes, "str.in_re", args.as_ref()),
        EggSmt::StrLen(args) => handle_application(nodes, "str.len", args.as_ref()),
        EggSmt::StrPrefixof(args) => handle_application(nodes, "str.prefixof", args.as_ref()),
        EggSmt::StrSubstr(args) => handle_application(nodes, "str.substr", args.as_ref()),
        EggSmt::StrSuffixof(args) => handle_application(nodes, "str.suffixof", args.as_ref()),
        EggSmt::StrToRe(args) => handle_application(nodes, "str.to_re", args.as_ref()),

        // Regex Operators
        EggSmt::ReStar(args) => handle_application(nodes, "re.*", args.as_ref()),
        EggSmt::ReConcat(args) => {
            regroup_nary_left(nodes, args, "re.++", make_extractor!(EggSmt::ReConcat))
        }
        EggSmt::ReUnion(args) => {
            regroup_nary_left(nodes, args, "re.union", make_extractor!(EggSmt::ReUnion))
        }

        // Math Operators
        EggSmt::Add(args) => regroup_nary_left(nodes, args, "+", make_extractor!(EggSmt::Add)),
        EggSmt::Sub(args) => regroup_nary_left(nodes, args, "-", make_extractor!(EggSmt::Sub)),
        EggSmt::Mul(args) => regroup_nary_left(nodes, args, "*", make_extractor!(EggSmt::Mul)),
        EggSmt::Div(args) => regroup_nary_left(nodes, args, "/", make_extractor!(EggSmt::Div)),
        EggSmt::IntDiv(args) => {
            regroup_nary_left(nodes, args, "div", make_extractor!(EggSmt::IntDiv))
        }
        EggSmt::Neg(args) => handle_application(nodes, "-", args.as_ref()),

        // Comparators
        EggSmt::Equal(args) => handle_application(nodes, "=", args.as_ref()),
        EggSmt::LessThan(args) => handle_application(nodes, "<", args.as_ref()),
        EggSmt::LessThanEqual(args) => handle_application(nodes, "<=", args.as_ref()),
        EggSmt::GreaterThan(args) => handle_application(nodes, ">", args.as_ref()),
        EggSmt::GreaterThanEqual(args) => handle_application(nodes, ">=", args.as_ref()),

        // Binary Operators
        EggSmt::BinaryAnd(args) => {
            regroup_nary_left(nodes, args, "bvand", make_extractor!(EggSmt::BinaryAnd))
        }

        // Other
        EggSmt::Attribute(packed) => handle_attribute(nodes, packed),
        EggSmt::AttributeValue(_) => {
            panic!("AttributeValues should not be occurring at the Term level")
        }
        EggSmt::Forall(packed) => handle_forall(nodes, packed),
        EggSmt::Let(packed) => handle_let(nodes, packed),
        EggSmt::Exists(packed) => handle_exists(nodes, packed),
        EggSmt::Identifier(packed) => ast::Term::QualIdentifier(ast::QualIdentifier::Simple {
            identifier: handle_identifier(nodes, packed),
        }),
        EggSmt::IdentifierApplication(packed) => handle_identifierapplication(nodes, packed),
        EggSmt::Application(sym, args) => handle_application(nodes, sym.to_string().as_str(), args),

        // Contradiction
        EggSmt::Contradiction(_) => {
            panic!("The poison node 'Contradiction' should never be in extracted RecExprs")
        }
    }
}

// +---------------------------------------------------------------------------------------------+
// | Helpers                                                                                     |
// +---------------------------------------------------------------------------------------------+

fn str_to_simple_qualidentifier(s: &str) -> ast::QualIdentifier {
    ast::QualIdentifier::Simple {
        identifier: ast::Identifier::Simple {
            symbol: ast::Symbol(s.to_string()),
        },
    }
}

fn handle_symbol(nodes: &[EggSmt], idx: Id) -> ast::Symbol {
    match &nodes[usize::from(idx)] {
        EggSmt::Symbol(s) => ast::Symbol(s.to_string()),
        other => panic!("Expected a Symbol, found: {}", other),
    }
}

fn handle_index(nodes: &[EggSmt], idx: Id) -> smt2parser::visitors::Index {
    match &nodes[usize::from(idx)] {
        EggSmt::Numeral(n) => smt2parser::visitors::Index::Numeral(n.clone()),
        EggSmt::Symbol(sym) => smt2parser::visitors::Index::Symbol(ast::Symbol(sym.to_string())),
        other => panic!("Index should only be a Numeral or Symbol, found: {}", other),
    }
}

fn handle_sort(nodes: &[EggSmt], idx: Id) -> ast::Sort {
    match &nodes[usize::from(idx)] {
        EggSmt::Symbol(s) => ast::Sort::Simple {
            identifier: ast::Identifier::Simple {
                symbol: ast::Symbol(s.to_string()),
            },
        },
        EggSmt::Application(sym, ids) => ast::Sort::Parameterized {
            identifier: ast::Identifier::Simple {
                symbol: ast::Symbol(sym.to_string()),
            },
            parameters: ids.iter().map(|i| handle_sort(nodes, *i)).collect(),
        },
        EggSmt::Identifier(packed) => ast::Sort::Simple {
            identifier: handle_identifier(nodes, packed),
        },
        other => panic!(
            "Sort should only be a Symbol, Application, or Identifier, found: {}",
            other
        ),
    }
}

fn handle_keyword(nodes: &[EggSmt], idx: Id) -> ast::Keyword {
    match &nodes[usize::from(idx)] {
        EggSmt::Symbol(sym) => ast::Keyword(sym.to_string()),
        other => panic!("Keywords should be symbols, found: {}", other),
    }
}

fn handle_attributevalue(nodes: &[EggSmt], idx: Id) -> ast::AttributeValue {
    match &nodes[usize::from(idx)] {
        EggSmt::AttributeValue(a) => a.val.clone(),
        other => panic!("Unexpected AttributeValue: {}", other),
    }
}

fn handle_identifier(nodes: &[EggSmt], packed: &[Id]) -> ast::Identifier {
    let (first, rest) = packed.split_first().unwrap();
    let symbol = handle_symbol(nodes, *first);
    let indices = rest.iter().map(|r| handle_index(nodes, *r)).collect();
    ast::Identifier::Indexed { symbol, indices }
}

fn handle_boolean(b: bool) -> ast::Term {
    ast::Term::QualIdentifier(ast::QualIdentifier::Simple {
        identifier: ast::Identifier::Simple {
            symbol: ast::Symbol(if b {
                "true".to_string()
            } else {
                "false".to_string()
            }),
        },
    })
}

fn regroup_nary_right(
    nodes: &[EggSmt],
    args: &[Id],
    op_str: &str,
    extractor: fn(&EggSmt) -> Option<&[Id; 2]>,
) -> ast::Term {
    let qual_identifier = str_to_simple_qualidentifier(op_str);
    let mut to_extract = args[1];
    let mut argument_ids = vec![args[0]];
    loop {
        let extracted = extractor(&nodes[usize::from(to_extract)]);
        match extracted {
            Some(args) => {
                argument_ids.push(args[0]);
                to_extract = args[1];
            }
            None => {
                argument_ids.push(to_extract);
                break;
            }
        }
    }
    let arguments = argument_ids
        .iter()
        .map(|id| handle_term(nodes, *id))
        .collect();
    ast::Term::Application {
        qual_identifier,
        arguments,
    }
}

fn regroup_nary_left(
    nodes: &[EggSmt],
    args: &[Id],
    op_str: &str,
    extractor: fn(&EggSmt) -> Option<&[Id; 2]>,
) -> ast::Term {
    let qual_identifier = str_to_simple_qualidentifier(op_str);
    let mut to_extract = args[0];
    let mut argument_ids = vec![args[1]];
    loop {
        let extracted = extractor(&nodes[usize::from(to_extract)]);
        match extracted {
            Some(args) => {
                argument_ids.push(args[1]);
                to_extract = args[0];
            }
            None => {
                argument_ids.push(to_extract);
                break;
            }
        }
    }
    let arguments = argument_ids
        .iter()
        .map(|id| handle_term(nodes, *id))
        .rev()
        .collect();
    ast::Term::Application {
        qual_identifier,
        arguments,
    }
}

/// This is a tricky function to write.
/// Instead of being called on the chainable operation it need to be called on the and that joins the operation.
fn _regroup_nary_chainable(
    _nodes: &[EggSmt],
    _args: &[Id],
    _op_str: &str,
    _extractor: fn(&EggSmt) -> Option<&[Id; 2]>,
) -> ast::Term {
    todo!("regroup chainable operations")
}
// +---------------------------------------------------------------------------------------------+
// | Other                                                                                       |
// +---------------------------------------------------------------------------------------------+

fn handle_attribute(nodes: &[EggSmt], packed: &[Id]) -> ast::Term {
    // Reminder: a ! holding n attributes is encoded as 2*n+1 items. The first item is the body, and the rest 2*n items are the attribute name, value pairs
    let (first, rest) = packed.split_first().unwrap();
    let term = Box::new(handle_term(nodes, *first));
    let attributes = rest
        .chunks_exact(2)
        .map(|pair| {
            (
                handle_keyword(nodes, pair[0]),
                handle_attributevalue(nodes, pair[1]),
            )
        })
        .collect();
    ast::Term::Attributes { term, attributes }
}

fn handle_forall(nodes: &[EggSmt], packed: &[Id]) -> ast::Term {
    // Reminder: forall has a similar encoding to let
    let vars = packed
        .chunks_exact(2)
        .map(|pair| (handle_symbol(nodes, pair[0]), handle_sort(nodes, pair[1])))
        .collect();
    let term = Box::new(handle_term(nodes, *packed.last().unwrap()));
    ast::Term::Forall { vars, term }
}

fn handle_let(nodes: &[EggSmt], packed: &[Id]) -> ast::Term {
    // Reminder: a let binding n symbols is encoded as 2*n+1 items. The first 2*n are the bindings and the last one is the body of the let
    let var_bindings = packed
        .chunks_exact(2)
        .map(|pair| (handle_symbol(nodes, pair[0]), handle_term(nodes, pair[1])))
        .collect();
    let term = Box::new(handle_term(nodes, *packed.last().unwrap()));
    ast::Term::Let { var_bindings, term }
}

fn handle_exists(nodes: &[EggSmt], packed: &[Id]) -> ast::Term {
    // Reminder: exists has a similar encoding to let
    let vars = packed
        .chunks_exact(2)
        .map(|pair| (handle_symbol(nodes, pair[0]), handle_sort(nodes, pair[1])))
        .collect();
    let term = Box::new(handle_term(nodes, *packed.last().unwrap()));
    ast::Term::Exists { vars, term }
}

fn handle_identifierapplication(nodes: &[EggSmt], packed: &[Id]) -> ast::Term {
    let (iden, args) = packed.split_first().unwrap();
    let new_packed = match &nodes[usize::from(*iden)] {
        EggSmt::Identifier(packed) => packed,
        other => panic!("Expected an identifier, found: {}", other),
    };
    let qual_identifier = ast::QualIdentifier::Simple {
        identifier: handle_identifier(nodes, new_packed),
    };
    let arguments = args.iter().map(|i| handle_term(nodes, *i)).collect();
    ast::Term::Application {
        qual_identifier,
        arguments,
    }
}

fn handle_application(nodes: &[EggSmt], name: &str, args: &[Id]) -> ast::Term {
    let qual_identifier = str_to_simple_qualidentifier(name);
    let arguments = args.iter().map(|i| handle_term(nodes, *i)).collect();
    ast::Term::Application {
        qual_identifier,
        arguments,
    }
}
