#!/usr/bin/env python3

import argparse
from os import path
import sys


def determine_extra_flags(query):
    extras = list()
    if "str." in query or "STRING_SUBSTR" in query:
        extras.append("--strings-exp")
    if "(get-value " in query or "(get-model)" in query:
        extras.append("--produce-models")
    return " ".join(extras)


def grok_query(query):
    string_replacements = {
        "bv2int": "bv2nat",
        "str.in.re": "str.in_re",
        "str.to.re": "str.to_re",
    }
    new_query = query
    for a, b in string_replacements.items():
        new_query = new_query.replace(a, b)
    if "(set-logic " not in new_query:
        new_query = "(set-logic ALL)\n" + new_query
    if "RegEx" in query and "(declare-sort RegEx 1)" not in query:
        # Punt and guess that the first right paren can be safely replaced
        new_query = new_query.replace(")", ")\n(declare-sort RegEx 1)", 1)

    bad_commands = {
        "(ext_rotate_left",
        "(ext_rotate_right",
        "(re.loop",
    }
    unsupported = any([b in new_query for b in bad_commands])
    return new_query, unsupported


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def parse_args(argv):
    arg_parser = argparse.ArgumentParser(
        description="Attempts to reformat an SMT query to be used with CVC5")

    help = "An SMT query file, use stdin if not present"
    arg_parser.add_argument("query_file", nargs="?", help=help)

    help = "Place to put the processed query"
    arg_parser.add_argument("--outfile", "-o", help=help)

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

    new_query, unsupported = grok_query(query)

    if args.outfile != None:
        with open(args.outfile, "w") as f:
            f.write(new_query)
    else:
        sys.stdout.write(new_query)

    return 0


if __name__ == "__main__":
    exit_code = 130
    try:
        exit_code = main(sys.argv)
    except KeyboardInterrupt:
        eprint("\nGoodbye\n")

    sys.exit(exit_code)
