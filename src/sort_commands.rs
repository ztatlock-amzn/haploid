use smt2parser::concrete as ast;
use smt2parser::concrete::Command;
use std::cmp::Ordering;

/// Sort the commands in a query to normalize them.
/// The sorting order is configuration commands, declares, defines, asserts, check sats, exit,
/// and finally some of the get commands.
/// Some commands are not supported, most notably push and pop.
/// Inside each section the commands are sorted by the string value of the command.
pub fn sort_commands(commands: &mut [Command]) {
    commands.sort_by(cmp_command_type);
}

/// Comparator based on the induced ordering of commands given by `command_type_order`
fn cmp_command_type(lhs: &Command, rhs: &Command) -> Ordering {
    let lhs_ord = command_type_order(lhs);
    let rhs_ord = command_type_order(rhs);
    // If they are different Commands then order is defined by command_type_order
    if lhs_ord != rhs_ord {
        lhs_ord.cmp(&rhs_ord)
    // if they are the same, but in the declar/define grouping don't reorder
    // this is to avoid moving a use of a type before its creation
    } else if 3 == lhs_ord {
        Ordering::Equal
    // Sort other matching command by string
    } else {
        lhs.to_string().cmp(&rhs.to_string())
    }
}

/// Assign order to command types
#[allow(unused_variables)]
fn command_type_order(cmd: &Command) -> usize {
    match cmd {
        // Configuration
        Command::SetLogic { symbol } => 0,
        Command::SetInfo { keyword, value } => 1,
        Command::SetOption { keyword, value } => 2,
        // Declares
        Command::DeclareSort { symbol, arity } => 3,
        Command::DeclareDatatype { symbol, datatype } => 3,
        Command::DeclareDatatypes { datatypes } => 3,
        Command::DeclareFun {
            symbol,
            parameters,
            sort,
        } => 3,
        Command::DeclareConst { symbol, sort } => 3,
        // Defines
        Command::DefineFun { sig, term } => 3,
        Command::DefineFunRec { sig, term } => 3,
        Command::DefineFunsRec { funs } => 3,
        Command::DefineSort {
            symbol,
            parameters,
            sort,
        } => 3,
        //  Asserts
        Command::Assert { term } => match term {
            ast::Term::Application {
                qual_identifier:
                    ast::QualIdentifier::Simple {
                        identifier: ast::Identifier::Simple { symbol },
                    },
                arguments,
            } => {
                if symbol.0 == "=" {
                    12
                } else {
                    13
                }
            }
            _ => 13,
        },
        // Check sat
        Command::CheckSat => 14,
        Command::CheckSatAssuming { literals } => 15,
        // Exit
        Command::Exit => 16,
        // Supported Gets
        Command::GetInfo { flag } => 17,
        Command::GetValue { terms } => 18,
        Command::GetModel => 19,
        // Below here are the unsupported command types.
        // Some we haven't needed yet.
        // Others will require rethinking how this sorting thing is done (reset, pop, ...)
        Command::Echo { message } => panic!("Echo not supported"),
        Command::GetAssertions => panic!("GetAssertions not supported"),
        Command::GetAssignment => panic!("GetAssignment not supported"),
        Command::GetOption { keyword } => panic!("GetOption not supported"),
        Command::GetProof => panic!("GetProof not supported"),
        Command::GetUnsatAssumptions => panic!("GetUnsetAssumptions not supported"),
        Command::GetUnsatCore => panic!("GetUnsatCore not supported"),
        Command::Pop { level } => panic!("Pop not supported"),
        Command::Push { level } => panic!("Push not supported"),
        Command::Reset => panic!("Reset not supported"),
        Command::ResetAssertions => panic!("ResetAssertions not supported"),
    }
}
