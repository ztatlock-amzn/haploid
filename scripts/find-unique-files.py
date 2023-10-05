#!/usr/bin/env python3

import argparse
import os
from os import path
import sys
import hashlib


def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)


def parse_args(argv):
    arg_parser = argparse.ArgumentParser(
        description="Lists files that have unique sha1 hashes")

    help = "Directory to search for files in"
    arg_parser.add_argument("directory", help=help)

    help = "File extension"
    arg_parser.add_argument("--extension", "-e", help=help, default="smt2")

    args = arg_parser.parse_args(args=argv[1:])

    if not path.isdir(args.directory):
        eprint(f"Input directory not found: '{args.directory}'")
        sys.exit(2)

    return args


def hash_file(filename):
    sha1 = hashlib.sha1()
    with open(filename, "rb") as f:
        data = f.read(2**16)
        while data:
            sha1.update(data)
            data = f.read(2**16)
    return sha1.hexdigest()


def main(argv):
    args = parse_args(argv)

    files = list()
    for (dirpath, dirnames, filenames) in os.walk(args.directory):
        files += [path.join(dirpath, file) for file in filenames]

    files = [f for f in files if f.endswith(args.extension)]

    hashes = dict()
    for file in files:
        hash = hash_file(file)
        if hash not in hashes:
            hashes[hash] = file
            print(file)

    return 0


if __name__ == "__main__":
    exit_code = 130
    try:
        exit_code = main(sys.argv)
    except KeyboardInterrupt:
        eprint("\nGoodbye\n")

    sys.exit(exit_code)
