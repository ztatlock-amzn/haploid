use std::{
    fs::File,
    io::{self, BufReader},
    path::Path,
};

use smt2parser::concrete::Command;

/// Parse input for command line
/// If no file then read from stdin
pub fn parse_input(maybe_filename: &Option<String>) -> Vec<Command> {
    match maybe_filename {
        Some(filename) => parse_file(filename),
        None => {
            let reader = BufReader::new(io::stdin());
            let stream = smt2parser::CommandStream::new(
                reader,
                smt2parser::concrete::SyntaxBuilder,
                Some("stdin".to_string()),
            );
            stream.map(|cmd| cmd.unwrap()).collect()
        }
    }
}

/// Parse the given filename as smt2
/// No errors are caught.
fn parse_file(filename: &String) -> Vec<Command> {
    let path = Path::new(filename);
    let file = match File::open(path) {
        Ok(f) => f,
        Err(_) => {
            eprintln!("Unable to find file: '{}'", &filename);
            std::process::exit(1);
        }
    };
    let reader = BufReader::new(file);
    let stream = smt2parser::CommandStream::new(
        reader,
        smt2parser::concrete::SyntaxBuilder,
        Some(filename.to_string()),
    );
    stream.map(|cmd| cmd.unwrap()).collect()
}
