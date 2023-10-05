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
        description="Haploid regression tester")

    help = "Either a file containing benchmark file names or a directory containing benchmarks"
    arg_parser.add_argument("benchmarks", help=help)

    help = "Time limit in seconds, Haploid will be killed with SIGKILL"
    arg_parser.add_argument("--timeout", "-t", help=help,
                            type=float, default=15.0)

    help = "Number of concurrent jobs to use"
    arg_parser.add_argument("--jobs", "-j", help=help, type=int, default=1)

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


def results_to_row(results=None, prefix=""):
    columns = list()

    # if no data is present return the header
    if results == None:
        columns.extend(
            ["Benchmark", "Result", "Time"])

    # otherwise return the row data with the benchmark's filename shortened
    else:
        columns.extend([results["benchmark"].replace(prefix, ""),
                        results["result"],
                        str(results["elapsed"])])

    return ",".join(columns)


def extract_expected(query):
    marker = ";; EXPECTED: "
    lines = [l.strip() for l in query.splitlines()]
    lines = [l for l in query.splitlines() if l != ""]
    expected_lines = [l[len(marker):].strip()
                      for l in lines if l.startswith(marker)]
    query_lines = [l for l in lines if not l.startswith(marker)]
    return "\n".join(query_lines), "\n".join(expected_lines)


def handle_benchmark(haploid, benchmark, timeout, prefix):
    # Get our working directory
    work_dir = tempfile.mkdtemp()

    try:
        # Read the query
        with open(benchmark, "r") as f:
            query = f.read()

        # Get the expected output
        query, expected = extract_expected(query)

        # Then we run Haploid
        rundata = run(f"{haploid} --in", work_dir, timeout, query)
        rundata["benchmark"] = benchmark

        actual = "\n".join([l.strip() for l in rundata["stdout"].splitlines()])

        if rundata["reached_timeout"]:
            rundata["result"] = "timeout"
        elif rundata["return_code"] != 0:
            eprint("-"*80)
            eprint(f"Command failed: {haploid}")
            eprint(f"Benchmark: {benchmark}")
            eprint(f"return_code: {rundata['return_code']}")
            eprint(f"stdout:\n{rundata['stdout']}")
            eprint(f"stderr:\n{rundata['stderr']}")
            eprint("-"*80)
            rundata["result"] = "crash"
        elif expected == actual:
            rundata["result"] = "pass"
        else:
            eprint("="*80)
            eprint(f"Test failed: {benchmark}")
            eprint(f"input:\n\n{query}\n")
            eprint(f"expected:\n\n{expected}\n")
            eprint(f"actual:\n\n{actual}\n")
            eprint("="*80)
            rundata["result"] = "fail"

    finally:
        # Delete the work directory
        shutil.rmtree(work_dir)

    return results_to_row(rundata, prefix)


def apply_callback(tup):
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


def get_worklist(benchmarks, extension):
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
        eprint("Ouput file exists, but is not a csv file for regression data")
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

    benchmark_files = get_worklist(args.benchmarks, "smt2")

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
        eprint("Building Haploid")
        run("cargo build --release", os.getcwd())
    args.haploid = path.abspath(args.haploid)

    eprint("Running benchmarks")

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
                args.haploid, file, args.timeout, prefix)
            apply_callback(row)
    else:
        with multiprocessing.Pool(processes=args.jobs) as pool:
            def error_callback(e):
                pool.terminate()
                raise e

            for file in benchmark_files:
                pool.apply_async(func=handle_benchmark,
                                 args=(args.haploid, file,
                                       args.timeout, prefix),
                                 callback=apply_callback,
                                 error_callback=error_callback)
            pool.close()
            pool.join()

    # Done
    return 0


if __name__ == "__main__":
    retcode = 130
    try:
        retcode = main(sys.argv)
    except KeyboardInterrupt:
        print("\nGoodbye\n", file=sys.stderr)

    sys.exit(retcode)
