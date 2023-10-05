use clap::{ArgGroup, Parser};
use haploid::{dump_commands, parse_input, split_assert_and};

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
    let query = split_assert_and(&query);
    dump_commands(&query, &args.out_filename);
}
