use smt2parser::concrete::Command;
use std::io::Write;

/// Print the smt2 query, either to a file or stdout
pub fn dump_commands(commands: &Vec<Command>, filename: &Option<String>) {
    match filename {
        Some(out_filename) => {
            let mut fp = std::fs::File::create(out_filename).unwrap();
            for line in commands {
                match writeln!(fp, "{}", line) {
                    Ok(_) => (),
                    Err(_) => return,
                }
            }
        }
        None => {
            for line in commands {
                println!("{}", line);
            }
        }
    };
}

/// Print the smt2 query, either to a file or stdout
/// todo: learn rust's types
pub fn dump_strings(commands: &Vec<String>, filename: &Option<String>) {
    match filename {
        Some(out_filename) => {
            let mut fp = std::fs::File::create(out_filename).unwrap();
            for line in commands {
                match writeln!(fp, "{}", line) {
                    Ok(_) => (),
                    Err(_) => return,
                };
            }
        }
        None => {
            for line in commands {
                println!("{}", line);
            }
        }
    };
}
