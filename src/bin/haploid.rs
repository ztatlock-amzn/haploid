use clap::{ArgGroup, Parser};
use haploid::{
    dump_commands, lift_assert_or_and, parse_input, simplify_asserts, sort_commands,
    split_assert_and,
};

/// Haploid uses the egg EGraph implementation to simplify SMT queries.
/// Some commands are not supported, such as `push`, `pop`, and `reset`.
#[derive(clap::Parser)]
#[clap(author = "Ian Briggs")]
#[clap(about = "EGraph based SMT simplifier")]
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

    /// Time limit in seconds
    #[clap(short, long, default_value_t = 1.5_f64)]
    time_limit: f64,

    /// Node limit for the EGraph
    #[clap(short, long, default_value_t = 10_000_usize)]
    node_limit: usize,

    /// How many iterations to be used for the EGraph
    #[clap(short, long, default_value_t = 5_usize)]
    iters: usize,
}

fn main() {
    env_logger::init();
    let args = Args::parse();
    let query = parse_input(&args.filename);
    let flat = split_assert_and(&query);
    let mut lifted = lift_assert_or_and(&flat);
    sort_commands(&mut lifted);
    let simplified = simplify_asserts(lifted, args.time_limit, args.node_limit, args.iters);
    dump_commands(&simplified, &args.out_filename);
}
