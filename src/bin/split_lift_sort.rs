use clap::{ArgGroup, Parser};
use haploid::{dump_commands, lift_assert_or_and, parse_input, sort_commands, split_assert_and};

/// A binary that just does the assertion pre-splitting and query sorting phases of Haploid
#[derive(clap::Parser)]
#[clap(author = "Ian Briggs")]
#[clap(about = "Pre-splitting and sorting")]
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
    dump_commands(&lifted, &args.out_filename);
}
