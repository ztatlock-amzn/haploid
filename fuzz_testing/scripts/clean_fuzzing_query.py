#!/usr/bin/env python3

import argparse
from hashlib import new
from os import path
import sys
import re


def grok_query(query):
    # remove unsupported commands
    commands_to_remove = {"(push", "(pop", "(reset",
                          "(reset-assertions", "(check-sat", "(check-sat-assuming",
                          "(match"}
    lines = [l for l in query.splitlines()
             if not any([c in l for c in commands_to_remove])]

    # add back in a check-sat
    exits = [i for i, l in enumerate(lines) if l.startswith("(exit)")]
    if len(exits) == 1:
        lines.insert(exits[0], "(check-sat)")
    elif len(exits) == 0:
        lines.append("(check-sat)")
    else:
        eprint("Query with multiple (exit) commands found")
        sys.exit(2)

    return "\n".join(lines) + "\n"


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def parse_args(argv):
    arg_parser = argparse.ArgumentParser(
        description="Force clean a fuzzing query, can change the meaning of the query")

    help = "An SMT query file, use stdin if not present"
    arg_parser.add_argument("query_file", help=help, nargs="?")

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

    new_query = grok_query(query)

    if args.outfile != None:
        with open(args.outfile, "w") as f:
            f.write(new_query)
    else:
        sys.stdout.write(new_query)

    return 0


if __name__ == "__main__":
    retcode = 130
    try:
        retcode = main(sys.argv)
    except KeyboardInterrupt:
        eprint("\nGoodbye\n")

    sys.exit(retcode)
