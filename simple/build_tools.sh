#!/bin/bash
# Build script for Simple formatter and linter
# Compiles .spl files to executables in simple/bin_simple/

set -e

echo "=== Building Simple Formatter & Linter ==="
echo ""

# Create output directories
mkdir -p simple/bin_simple
mkdir -p simple/build

# Check if simple compiler is available
if ! command -v ./simple/bin/simple &> /dev/null; then
    echo "Error: Simple compiler not found at ./simple/bin/simple"
    echo "Please build the compiler first: cargo build"
    exit 1
fi

SIMPLE_COMPILER="./simple/bin/simple"

# Build formatter
echo "Building formatter..."
$SIMPLE_COMPILER compile simple/app/formatter/main.spl \
    --output simple/bin_simple/simple_fmt \
    --build-dir simple/build/formatter \
    || { echo "Failed to build formatter"; exit 1; }

echo "✓ Formatter built: simple/bin_simple/simple_fmt"

# Build linter  
echo "Building linter..."
$SIMPLE_COMPILER compile simple/app/lint/main.spl \
    --output simple/bin_simple/simple_lint \
    --build-dir simple/build/lint \
    || { echo "Failed to build linter"; exit 1; }

echo "✓ Linter built: simple/bin_simple/simple_lint"

echo ""
echo "=== Build Complete ==="
echo ""
echo "Executables:"
echo "  simple/bin_simple/simple_fmt  - Formatter"
echo "  simple/bin_simple/simple_lint - Linter"
echo ""
echo "Usage:"
echo "  ./simple/bin_simple/simple_fmt <file.spl> [--check] [--write]"
echo "  ./simple/bin_simple/simple_lint <file.spl> [--deny-all]"
echo ""
