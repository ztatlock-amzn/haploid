#!/usr/bin/env python3

import argparse
import multiprocessing
from os import path
import shlex
import signal
import subprocess
import sys
import time
from clean_fuzzing_query import grok_query

SCRIPTS_DIR = path.dirname(path.abspath(__file__))
FUZZ_DIR = path.split(SCRIPTS_DIR)[0]
MURXLA_DIR = path.join(FUZZ_DIR, "murxla")
MURXLA = path.join(MURXLA_DIR, "build", "bin", "murxla")
PROFILE = path.join(MURXLA_DIR, "src", "solver", "cvc5", "profile.json")
CVC5 = "cvc5 --strings-exp --fp-exp --sets-ext --incremental"


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def parse_args(argv):
    arg_parser = argparse.ArgumentParser(
        description="Fuzz haploid components for bugs")

    help = "Haploid bin directory"
    arg_parser.add_argument("directory", help=help)

    help = "Starting seed to use for murxla"
    arg_parser.add_argument("--seed", help=help, type=int, default=1)

    help = "Solver command used to determine if Haploid changed sat-ness"
    arg_parser.add_argument("--solver", help=help, default=CVC5)

    help = "Timeout for solver"
    arg_parser.add_argument("--timeout", help=help, default=3)

    help = "Stop fuzzing when an error is in Haploid"
    arg_parser.add_argument("--stop", "-s", help=help, action="store_true")

    help = "Don't create files for errors in the solver/murxla"
    arg_parser.add_argument("--skip", help=help, action="store_true")

    help = "Number of concurrent jobs to use"
    arg_parser.add_argument("--jobs", "-j", help=help, type=int, default=1)

    help = "Target number of passing tests (0 for no limit)"
    arg_parser.add_argument("--passing", "-p", help=help, type=int, default=0)

    args = arg_parser.parse_args(args=argv[1:])

    if not path.isfile(MURXLA):
        eprint(f"Murxla not found at: '{MURXLA}'")
        eprint("Please build murxla")
        sys.exit(2)

    if not path.isdir(args.directory):
        eprint(f"Haploid bin directory not found at: '{args.directory}'")
        sys.exit(2)

    return args


def run(cmd, timeout, stdin=None):
    command = shlex.split(cmd)
    reached_timeout = False
    start_time = time.perf_counter()
    proc = subprocess.Popen(command,
                            bufsize=1,
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            universal_newlines=True)
    try:
        stdout, stderr = proc.communicate(input=stdin, timeout=timeout)
    except subprocess.TimeoutExpired:
        reached_timeout = True
        proc.kill()
        stdout, stderr = proc.communicate()

    end_time = time.perf_counter()

    return_code = proc.returncode

    elapsed = end_time - start_time

    return {
        "command": " ".join(command),
        "stdout": stdout,
        "stderr": stderr,
        "return_code": return_code,
        "elapsed": elapsed,
        "reached_timeout": reached_timeout,
    }


def dump_file(prefix, seed, query):
    file = f"{prefix}_murxla_seed_{seed}.smt2"
    with open(file, "w") as f:
        f.write(query)
    return file


def first_line(text):
    lines = text.splitlines()
    if len(lines) == 0:
        return ""
    if len(lines) == 1:
        return lines[0]
    return f"{lines[0]} ..."


def dump_run_data(run_data, file_or_seed):
    eprint("\n")
    if type(file_or_seed) == int:
        eprint(f"Seed: {file_or_seed}")
    else:
        eprint(f"File: {file_or_seed}")
    eprint(f"  Command: {run_data['command']}")
    eprint(f"  Return code: {run_data['return_code']}")
    eprint(f"  Stdout: {first_line(run_data['stdout'])}")
    eprint(f"  Stderr: {first_line(run_data['stderr'])}")
    eprint("\n")


class FoundCrash(Exception):
    pass


def fuzz_seed(seed, bin_dir, timeout, solver, stop, skip):
    # Generate the query
    murxla_rundata = run(
        f"{MURXLA} --seed {seed} --profile {PROFILE}", timeout)
    if murxla_rundata["reached_timeout"]:
        return seed, "murxla_timeout"
    if murxla_rundata["return_code"] != 0:
        if "Assertion `false' failed" in murxla_rundata["stderr"]:
            return seed, "murxla_assertion_failure"
        return seed, "murxla_crash"

    query = murxla_rundata["stdout"]

    # Run with the solver to check that the solver is okay with it
    solver_rundata = run(solver, timeout, query)
    if solver_rundata["reached_timeout"]:
        return seed, "solver_timeout"
    if solver_rundata["return_code"] != 0:
        if not skip:
            dump_file("solver_crash", seed, query)
        return seed, "solver_crash_or_invalid_smt"

    solver_answer = solver_rundata["stdout"]

    # Use the cleaning code and check that it didn't break the query
    clean_query = grok_query(query)
    clean_solver_rundata = run(solver, timeout, clean_query)
    if clean_solver_rundata["reached_timeout"]:
        return seed, "clean_caused_solver_timeout"
    if clean_solver_rundata["return_code"] != 0:
        return seed, "clean_caused_invalid_smt"

    # Check that the parsing code can handle it
    parser_rundata = run(f"{bin_dir}/just_parse --in", timeout, clean_query)
    if parser_rundata["reached_timeout"]:
        return seed, "parser_timeout"
    if parser_rundata["return_code"] != 0:
        #dump_file("parser_crash", seed, clean_query)
        return seed, "parser_crash"

    # Check that Haploid can handle it
    haploid_rundata = run(f"{bin_dir}/haploid --in", timeout, clean_query)
    if haploid_rundata["reached_timeout"]:
        return seed, "haploid_timeout"
    if haploid_rundata["return_code"] != 0:
        file = dump_file("haploid_crash", seed, clean_query)
        dump_run_data(haploid_rundata, file)
        if stop:
            raise FoundCrash(f"Haploid crashed on input '{file}'")
        return seed, "haploid_crash"

    haploid_query = haploid_rundata["stdout"]

    # Check that Haploid didn't cause a crash in the solver
    haploid_solver_rundata = run(solver, timeout, haploid_query)
    if haploid_solver_rundata["reached_timeout"]:
        return seed, "haploid_caused_timeout"
    if haploid_solver_rundata["return_code"] != 0:
        file = dump_file("haploid_caused_crash", seed, clean_query)
        dump_run_data(haploid_rundata, file)
        if stop:
            raise FoundCrash(f"Haploid broke SMT on input '{file}'")
        return seed, "haploid_caused_crash"

    haploid_solver_answer = solver_rundata["stdout"]

    # Check that Haploid didn't change the meaning of the query
    if haploid_solver_answer != solver_answer:
        file = dump_file("haploid_changed_result", seed, clean_query)
        eprint("\n")
        eprint("Haploid changed the meaning of a query")
        eprint(f"Query: {file}")
        eprint(f"Solver out:\n{solver_answer}")
        eprint(f"Haploid plus solver out:\n{haploid_solver_answer}")
        eprint("\n")
        if ("unknown" not in haploid_solver_answer
            and "unknown" not in solver_answer
                and stop):
            raise FoundCrash(
                f"Haploid changed the meaning of the input '{file}'")
        return seed, "haploid_changed_result"

    return seed, "pass"


def wrapped_fuzz_seed(seed, bin_dir, timeout, solver, stop, skip):
    try:
        return fuzz_seed(seed, bin_dir, timeout, solver, stop, skip)
    except KeyboardInterrupt as e:
        return e
    except FoundCrash as e:
        return e
    except Exception as e:
        raise e


PASSED = 0
PASSED_GOAL = None


class ReachedGoal(Exception):
    pass


def print_result(tup):
    global PASSED
    if type(tup) == KeyboardInterrupt:
        return
    seed, result = tup
    if result == "pass":
        PASSED += 1
    if PASSED > PASSED_GOAL:
        raise ReachedGoal()
    print(f"{seed}\t{result}", flush=True)


def main(argv):
    global PASSED_GOAL
    args = parse_args(argv)
    bin_dir = args.directory
    timeout = args.timeout
    solver = args.solver
    stop = args.stop
    skip = args.skip
    seed = args.seed - 1
    PASSED_GOAL = args.passing

    print("Seed\tResult")
    if args.jobs == 1:
        while 1:
            seed += 1
            try:
                tup = fuzz_seed(seed, bin_dir, timeout, solver, stop, skip)
                print_result(tup)
            except FoundCrash as e:
                eprint(e.args[0])
                return 1

    else:
        with multiprocessing.Pool(processes=args.jobs) as pool:
            async_results = list()
            while 1:
                seed += 1
                res = pool.apply_async(func=wrapped_fuzz_seed,
                                       args=(seed, bin_dir, timeout,
                                             solver, stop, skip),
                                       callback=print_result)
                async_results.append(res)

                while len(async_results) > 100*args.jobs:
                    async_results = [
                        res for res in async_results if not res.ready()]
                    if len(async_results) > 100*args.jobs:
                        time.sleep(timeout)

    return 0


if __name__ == "__main__":
    retcode = 130
    try:
        retcode = main(sys.argv)
    except KeyboardInterrupt:
        eprint("\nGoodbye\n")

    sys.exit(retcode)
