use smt2parser::concrete as ast;

/// Match: (assert (or (and a b) (and a c) (and a d) ...))
/// Replace: (assert a) (assert (or b c d ...))
pub fn lift_assert_or_and(commands: &Vec<ast::Command>) -> Vec<ast::Command> {
    let mut new_commands = vec![];
    for command in commands {
        match command {
            ast::Command::Assert { term } => match match_or_and(term) {
                Some((always_true, or_expression)) => {
                    new_commands.push(ast::Command::Assert {
                        term: always_true.clone(),
                    });
                    new_commands.push(ast::Command::Assert {
                        term: or_expression,
                    });
                }
                None => new_commands.push(command.clone()),
            },
            _ => new_commands.push(command.clone()),
        }
    }
    new_commands
}

pub fn match_or_and(term: &ast::Term) -> Option<(&ast::Term, ast::Term)> {
    match term {
        ast::Term::Application {
            qual_identifier:
                ast::QualIdentifier::Simple {
                    identifier: ast::Identifier::Simple { symbol },
                },
            arguments,
        } => match symbol.0.as_str() {
            "or" => match_and(arguments),
            _ => None,
        },
        _ => None,
    }
}

fn match_and(arguments: &[ast::Term]) -> Option<(&ast::Term, ast::Term)> {
    let (first, rest) = arguments.split_first().unwrap();
    let (common_term, first_or) = match split_and(first) {
        Some((at, fo)) => (at, fo),
        None => return None,
    };
    let mut or_terms = vec![first_or.clone()];
    for maybe_and in rest {
        let (same, next_or) = match split_and(maybe_and) {
            Some((s, no)) => (s, no),
            None => return None,
        };
        if same != common_term {
            return None;
        }
        or_terms.push(next_or.clone());
    }
    Some((
        common_term,
        ast::Term::Application {
            qual_identifier: ast::QualIdentifier::Simple {
                identifier: ast::Identifier::Simple {
                    symbol: ast::Symbol("or".to_string()),
                },
            },
            arguments: or_terms,
        },
    ))
}

fn split_and(maybe_and: &ast::Term) -> Option<(&ast::Term, &ast::Term)> {
    match maybe_and {
        ast::Term::Application {
            qual_identifier:
                ast::QualIdentifier::Simple {
                    identifier: ast::Identifier::Simple { symbol },
                },
            arguments,
        } => match symbol.0.as_str() {
            "and" => {
                if arguments.len() == 2 {
                    Some((&arguments[0], &arguments[1]))
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}
