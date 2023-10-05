use clap::{ArgGroup, Parser};
use haploid::{
    ast_to_recexpr, dump_strings, lift_assert_or_and, parse_input, recexpr_to_ast, sort_commands,
    split_assert_and,
};

/// A binary that just does the assertion pre-splitting phase of Haploid
#[derive(clap::Parser)]
#[clap(author = "Ian Briggs")]
#[clap(about = "Pre-splitting")]
#[clap(version)]
#[clap(group(ArgGroup::new("input").required(true).args(&["filename", "use-stdin"])))]
struct Args {
    /// Input SMT format file
    #[clap()]
    filename: Option<String>,

    /// Use stdin for input
    #[clap(long = "in")]
    use_stdin: bool,

    /// Output filename
    #[clap(short, long)]
    out_filename: Option<String>,
}

fn main() {
    env_logger::init();
    let args = Args::parse();
    let query = parse_input(&args.filename);
    let flat = split_assert_and(&query);
    let mut lifted = lift_assert_or_and(&flat);
    sort_commands(&mut lifted);
    let tripped = lifted
        .iter()
        .map(|cmd| match cmd {
            smt2parser::concrete::Command::Assert { term } => {
                let middle = ast_to_recexpr(term);
                let after = recexpr_to_ast(&middle);
                format!("(assert {})", &after)
            }
            other => other.to_string(),
        })
        .collect();
    dump_strings(&tripped, &args.out_filename);
}
