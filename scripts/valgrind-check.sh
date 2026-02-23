#!/bin/bash
# Valgrind memory check for Simple compiler binaries
#
# Usage:
#   scripts/valgrind-check.sh                           # checks build/simple --version
#   scripts/valgrind-check.sh build-asan/simple          # specific binary
#   scripts/valgrind-check.sh build/simple test foo.spl  # binary with args

set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SUPP_FILE="$DIR/src/compiler_cpp/sanitizers/lsan.supp"

if [ $# -eq 0 ]; then
    BINARY="$DIR/build/simple"
    ARGS="--version"
else
    BINARY="$1"
    shift
    if [ $# -eq 0 ]; then
        ARGS="--version"
    else
        ARGS="$*"
    fi
fi

if [ ! -f "$BINARY" ]; then
    echo "Error: Binary not found: $BINARY"
    echo "Build first: cmake -B build -G Ninja -S src/compiler_cpp && ninja -C build"
    exit 1
fi

if ! command -v valgrind >/dev/null 2>&1; then
    echo "Error: valgrind not found. Install with: sudo apt-get install valgrind"
    exit 1
fi

VALGRIND_OPTS="--leak-check=full --show-leak-kinds=all --track-origins=yes --error-exitcode=1"

if [ -f "$SUPP_FILE" ]; then
    VALGRIND_OPTS="$VALGRIND_OPTS --suppressions=$SUPP_FILE"
fi

echo "=== Valgrind Memory Check ==="
echo "Binary: $BINARY"
echo "Args:   $ARGS"
echo ""

export SIMPLE_LIB="$DIR/src"
export SIMPLE_VERSION=$(cat "$DIR/VERSION" 2>/dev/null || echo "unknown")

valgrind $VALGRIND_OPTS "$BINARY" $ARGS
