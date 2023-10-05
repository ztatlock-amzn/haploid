use smt2parser::concrete::{Command, Term};

/// Split all commands of the form `(assert (and <thing> <other>))`
/// into multiple asserts `(assert <thing>) (assert <other>)`
///
/// The output commands should not contain any commands that start
/// `(assert (and`
pub fn split_assert_and(commands: &Vec<Command>) -> Vec<Command> {
    let mut new_commands = vec![];
    for command in commands {
        match command {
            Command::Assert { term: t } => {
                new_commands.extend(split_and(t.clone()));
            }
            _ => {
                new_commands.push(command.clone());
            }
        }
    }
    new_commands
}

/// Split a single command of the form `(assert (and <thing> <other>))`
/// into a vector of multiple asserts [`(assert <thing>)`, `(assert <other>)`]
///
/// The output vector should not contain ant commands that start `(assert (and`
fn split_and(assert_and: Term) -> Vec<Command> {
    // There may be many ands in the asserted statement, e.g. `(assert (and a (and b c)))`,
    // so we need to make sure these are all split
    let mut done = vec![];
    let mut work_stack = vec![assert_and];
    while !work_stack.is_empty() {
        let term = work_stack.pop().unwrap();
        match term {
            Term::Application {
                qual_identifier: ref qi,
                arguments: ref args,
            } => {
                if qi.to_string() == "and" {
                    work_stack.extend(args.clone());
                } else if qi.to_string() == "=" && args.len() > 2 {
                    for pair in args.windows(2) {
                        done.push(Command::Assert {
                            term: Term::Application {
                                qual_identifier: qi.clone(),
                                arguments: pair.to_vec(),
                            },
                        })
                    }
                } else {
                    done.push(Command::Assert { term });
                }
            }
            _ => {
                done.push(Command::Assert { term });
            }
        }
    }
    done.reverse(); // Since we use a stack the order got reversed.
    done
}
