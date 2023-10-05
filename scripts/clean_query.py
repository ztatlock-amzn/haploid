#!/usr/bin/env python3

import argparse
from hashlib import new
from os import path
import sys
import re


def grok_query(query):
    to_replace = {
        "str.in.re": "str.in_re",
        "str.to.re": "str.to_re",
    }
    to_delete = [
        # Overfit
        "(get-info :reason-unknown)\n(get-value ((ControlFlow 0 0)))\n(pop 1)\n; Undetermined\n(reset)\n(set-option :rlimit 0)\n; did a full reset\n(reset)",
        "(set-option :rlimit 0)",  # Causes some issues
        # Only applicable if the result is unknown
        "(get-info :reason-unknown)",
    ]
    new_query = query
    for a, b in to_replace.items():
        new_query = new_query.replace(a, b)

    for d in to_delete:
        if d in new_query:
            new_query = new_query.replace(d, "")

    # We control the timeout
    if "(set-option :timeout" in new_query:
        new_query = re.sub(r"\(set-option :timeout \d*\)", "", new_query)

    # A push, but no pop
    if new_query.count("(push 1)") == 1 and new_query.count("(pop 1)") == 0:
        new_query = new_query.replace("(push 1)", "", 1)

    # Some queries don't have a check-sat
    if "(check-sat)" not in new_query:
        new_query = new_query + "\n(check-sat)"

    return new_query


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def parse_args(argv):
    arg_parser = argparse.ArgumentParser(
        description="Attempts to clean an SMT query to not have some commands")

    help = "An SMT query file, use stdin if not present"
    arg_parser.add_argument("query_file", help=help, nargs="?")

    help = "Place to put the processed query"
    arg_parser.add_argument("--outfile", "-o", help=help)

    help = "Panic after output if all push/pop commands cannot be removed"
    arg_parser.add_argument("--panic", "-p", help=help,
                            default=False, action="store_true")

    args = arg_parser.parse_args(args=argv[1:])

    if (args.query_file != None
            and not path.isfile(args.query_file)):
        eprint(f"Input file not found: '{args.query_file}'")
        sys.exit(2)

    return args


def main(argv):
    args = parse_args(argv)

    query = list()
    if args.query_file != None:
        with open(args.query_file, "r") as f:
            query = f.read()
    else:
        query = sys.stdin.read()

    new_query = grok_query(query)

    if args.outfile != None:
        with open(args.outfile, "w") as f:
            f.write(new_query)
    else:
        sys.stdout.write(new_query)

    if args.panic:
        bad = ["(push", "(pop", "(reset)"]
        if any([b in new_query for b in bad]):
            eprint("Unable to remove all unwanted commands")
            return 1

    return 0


if __name__ == "__main__":
    exit_code = 130
    try:
        exit_code = main(sys.argv)
    except KeyboardInterrupt:
        eprint("\nGoodbye\n")

    sys.exit(exit_code)
