#!/usr/bin/env python3

import argparse
from os import path
import sys


def determine_extra_flags(query):
    return ""


def grok_query(query):
    string_replacements = {
        "(declare-sort RegEx 1)": "",
    }
    new_query = query
    for a, b in string_replacements.items():
        new_query = new_query.replace(a, b)
    return new_query, False


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def parse_args(argv):
    arg_parser = argparse.ArgumentParser(
        description="Attempts to reformat an SMT query to be used with Z3 version 4.8.17")

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
