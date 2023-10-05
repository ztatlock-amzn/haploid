use clap::{ArgGroup, Parser};
use haploid::{dump_commands, lift_assert_or_and, parse_input};

/// A binary that just does the assertion or-and lifting phase of Haploid
#[derive(clap::Parser)]
#[clap(author = "Ian Briggs")]
#[clap(about = "(or (and same a) (and same b) (and same c) ...) => (and same (or a b c ...))")]
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
    let lifted = lift_assert_or_and(&query);
    dump_commands(&lifted, &args.out_filename);
}
