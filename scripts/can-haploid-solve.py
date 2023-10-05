#!/usr/bin/env python3

import tempfile
import argparse
import time
import os
import os.path as path
import multiprocessing
import shlex
import shutil
import subprocess
import sys

import clean_query

OUTFILE = None


def parse_args(argv):
    arg_parser = argparse.ArgumentParser(
        description="Quantify how much Haploid can solve queries")

    help = "Either a file containing benchmark file names or a directory containing benchmarks"
    arg_parser.add_argument("benchmarks", help=help)

    help = "Time limit in seconds, Haploid will be killed with SIGKILL"
    arg_parser.add_argument("--timeout", "-t", help=help,
                            type=float, default=15.0)

    help = "Number of concurrent jobs to use"
    arg_parser.add_argument("--jobs", "-j", help=help, type=int, default=1)

    help = "File extension for benchmarks"
    arg_parser.add_argument("--extension", help=help, default="smt2")

    help = "Don't run 'cargo build --release'"
    arg_parser.add_argument("--no-build", help=help,
                            default=False, action="store_true")

    help = "A Haploid binary to use"
    arg_parser.add_argument("--haploid", help=help,
                            default="./target/release/haploid")

    help = "Output file to use, if present will be used to continue data run"
    arg_parser.add_argument("--outfile", "-o", help=help)

    args = arg_parser.parse_args(args=argv[1:])

    if args.outfile != None and not path.isfile(args.outfile):
        eprint(f"Creating new output file: '{args.outfile}'")

    return args


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def run(cmd, work_dir, timeout=None, stdin=None):
    command = shlex.split(cmd)
    start_dir = os.getcwd()
    reached_timeout = False
    os.chdir(work_dir)
    proc = None
    try:
        start_time = time.perf_counter()
        proc = subprocess.Popen(command,
                                stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                universal_newlines=True)
        stdout, stderr = proc.communicate(input=stdin, timeout=timeout)
    except subprocess.TimeoutExpired:
        reached_timeout = True
        proc.kill()
        stdout, stderr = proc.communicate()
    except FileNotFoundError as e:
        eprint(f"Unable to run command: '{command}'")
        eprint(f"Current directory: '{os.getcwd()}'")
        raise e
    finally:
        end_time = time.perf_counter()
        if proc:
            proc.kill()
        os.chdir(start_dir)

    return_code = proc.returncode

    elapsed = end_time - start_time

    return {
        "stdout": stdout,
        "stderr": stderr,
        "return_code": return_code,
        "elapsed": elapsed,
        "reached_timeout": reached_timeout,
    }


def count_asserts(query):
    # We want asserts that are not just binding a variable name to a value
    # TODO: this may remove too many asserts
    lines = query.splitlines()
    lines = [l.strip() for l in lines]
    lines = [l for l in lines if l.startswith("(assert")]
    # We only have lines starting with (assert
    # We need to remove lines that directly define a variable as a literal
    # Doing this without parsing is hard
    # Since this is made to judge if Haploid solved a query, we have some insignt:
    #  * haploid will always put a variable as the lhs in (assert (= <lhs> <rhs>))
    not_equals = [l for l in lines if not l.startswith("(assert (=")]
    not_variable_assigns = [l for l in lines if
                            # means lhs is a computation
                            (l.startswith("(assert (= (")
                             # means lhs is true and rhs is a computation
                             or l.startswith("(assert (= true (")
                                # means lhs is false and rhs is a computationa
                                or l.startswith("(assert (= false (")
                                # means lhs is a string
                                or l.startswith("(assert (= \"")
                             )]
    return len(not_equals) + len(not_variable_assigns)


def run_preprocessor(benchmark, preprocessor, work_dir, query, timeout):
    # Run the solver
    run_data = run(f"{preprocessor} --in", work_dir, timeout, query)
    run_data["benchmark"] = benchmark

    if (run_data["return_code"] == -9
            and run_data["reached_timeout"]):
        run_data["asserts_left"] = None
        return run_data

    if run_data["return_code"] != 0:
        eprint("-"*80)
        eprint(f"Command failed: {preprocessor}")
        eprint(f"Benchmark: {benchmark}")
        eprint(f"return_code: {run_data['return_code']}")
        eprint(f"stdout:\n{run_data['stdout']}")
        eprint(f"stderr:\n{run_data['stderr']}")
        eprint("-"*80)
        run_data["asserts_left"] = None
        return run_data

    if "(assert false)" in run_data["stdout"]:
        run_data["asserts_left"] = 0
        return run_data

    run_data["asserts_left"] = count_asserts(run_data["stdout"])
    return run_data


def results_to_row(results=None, prefix=""):
    columns = list()

    # if no data is present return the header
    if results == None:
        columns.extend(
            ["Benchmark", "AssertsBefore", "AssertsLeft", "Time", "Result"])

    # otherwise return the row data with the benchmark's filename shortened
    else:
        columns.extend([results["benchmark"].replace(prefix, ""),
                        str(results["asserts_before"]),
                        str(results["asserts_left"]),
                        str(results["elapsed"]),
                        results["result"]])

    return ",".join(columns)


def handle_benchmark(haploid, splitter, file, timeout, prefix):
    # Get our working directory
    work_dir = tempfile.mkdtemp()

    try:
        # Read the query
        with open(file, "r") as f:
            query = f.read()

        # Clean the query and exit if it failed
        cleaned = clean_query.grok_query(query)
        bad = ["(push", "(pop", "(reset)"]
        if any([b in cleaned for b in bad]):
            return None

        # Run the splitter
        split_data = run_preprocessor(file, splitter, work_dir, query, timeout)

        # Then we run Haploid
        row_data = run_preprocessor(file, haploid, work_dir,
                                    query, timeout)

        row_data["asserts_before"] = split_data["asserts_left"]
        row_data["result"] = "unknown"

        if row_data["reached_timeout"]:
            row_data["asserts_left"] = row_data["asserts_before"]
            row_data["result"] = "timeout"

        elif row_data["asserts_left"] == None:
            row_data["asserts_left"] = row_data["asserts_before"]
            row_data["result"] = "crash"

        elif "(assert false)" in row_data["stdout"]:
            row_data["result"] = "unsat"

        elif row_data["asserts_left"] == 0:
            row_data["result"] = "sat"

    finally:
        # Delete the work directory
        shutil.rmtree(work_dir)

    return results_to_row(row_data, prefix)


def apply_callback(tup):
    # Early out for failed runs
    if tup == None:
        return

    # Decide if we output to stdout or a file
    if OUTFILE == None:
        print(tup, flush=True)
    else:
        with open(OUTFILE, "a") as f:
            f.write(f"{tup}\n")


def sanitize_file_list(files, extension):
    # Clean and get the absolute path
    files = [f.strip() for f in files]
    files = [f for f in files if f != ""]
    files = [f for f in files if f[0] != "#"]
    files = [f for f in files if f.endswith(extension)]
    return [path.abspath(f) for f in files]


def get_work_list(benchmarks, extension):
    # Turn the input into a list of smt2 files
    benchmark_files = None

    # A single smt2 file
    if path.isfile(benchmarks) and path.splitext(benchmarks)[1][1:] == extension:
        benchmark_files = [benchmarks]

    # A file with a list of smt2 files
    elif path.isfile(benchmarks):
        with open(benchmarks, "r") as f:
            benchmark_files = f.readlines()

    # A directory we will recursively search for smt2 files
    elif path.isdir(benchmarks):
        benchmark_files = list()
        for (dirpath, dirnames, filenames) in os.walk(benchmarks):
            benchmark_files += [path.join(dirpath, file) for file in filenames]

    # User error
    else:
        eprint(f"Error: Input does not exist: '{benchmarks}'")
        sys.exit(2)

    benchmark_files = sanitize_file_list(benchmark_files, extension)
    return benchmark_files


def get_finished_runs(outfile):
    # Early out
    if not path.exists(outfile):
        return list()

    # Get csv data
    with open(outfile, "r") as f:
        lines = f.readlines()

    # Check that the first line is our header
    if lines[0] != results_to_row(None) + "\n":
        eprint("Output file exists, but is not a csv file for benchmark data")
        eprint(f"Expected first line: '{results_to_row(None)}'")
        eprint(f"Actual first line:   '{lines[0]}'")
        sys.exit(2)

    # Return a list of just the benchmark names
    rows = [row.split(",") for row in lines[1:]]
    benchmarks = [row[0] for row in rows]
    return benchmarks


def main(argv):
    global OUTFILE

    args = parse_args(argv)
    OUTFILE = args.outfile

    benchmark_files = get_work_list(args.benchmarks, args.extension)

    # Find a common prefix to make our output nicer
    common = path.commonprefix(benchmark_files)
    common_dir = path.split(common)[0]
    prefix = path.split(common_dir)[0]

    # Remove already run benchmarks
    if args.outfile != None:
        to_remove = get_finished_runs(args.outfile)
        for tr in to_remove:
            full = f"{prefix}{tr}"
            if full in benchmark_files:
                benchmark_files.remove(full)

    # Make sure the preprocessor bin is up to date
    if args.haploid != "./target/release/haploid" and not args.no_build:
        run("cargo build --release", os.getcwd())
    args.haploid = path.abspath(args.haploid)

    splitter = path.abspath("./target/release/split")

    # Print out header
    header = results_to_row()
    if args.outfile == None:
        print(header)
    elif not path.exists(args.outfile):
        with open(args.outfile, "w") as f:
            f.write(f"{header}\n")

    # Run the benchmarks
    if args.jobs == 1:
        for file in benchmark_files:
            row = handle_benchmark(
                args.haploid, splitter, file, args.timeout, prefix)
            apply_callback(row)
    else:
        with multiprocessing.Pool(processes=args.jobs) as pool:
            def error_callback(e):
                pool.terminate()
                raise e

            for file in benchmark_files:
                pool.apply_async(func=handle_benchmark,
                                 args=(args.haploid, splitter, file,
                                       args.timeout, prefix),
                                 callback=apply_callback,
                                 error_callback=error_callback)
            pool.close()
            pool.join()

    # Done
    return 0


if __name__ == "__main__":
    exit_code = 130
    try:
        exit_code = main(sys.argv)
    except KeyboardInterrupt:
        print("\nGoodbye\n", file=sys.stderr)

    sys.exit(exit_code)
