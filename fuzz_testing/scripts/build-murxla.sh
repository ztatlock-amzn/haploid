#!/usr/bin/env bash

set -e

SCRIPT_DIR=$(dirname "${0}")
FUZZ_DIR=$(cd "${SCRIPT_DIR}" && cd .. && pwd)

cd "${FUZZ_DIR}" || exit 2
rm -rf murxla
git clone https://github.com/murxla/murxla.git

cd murxla || exit 2
mkdir build

cd build || exit 2
cmake ..
make
