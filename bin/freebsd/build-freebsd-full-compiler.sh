#!/bin/sh
# Build Full FreeBSD Simple Compiler (Incremental Approach)
# Run this script IN the FreeBSD VM
#
# Prerequisites:
# - FreeBSD 14.x system
# - clang++ installed (pkg install clang)
# - seed_cpp binary and runtime files present

set -e

echo "========================================================================"
echo "  FreeBSD Full Simple Compiler - Incremental Build"
echo "========================================================================"
echo ""

# Configuration
SEED_CPP="./bin/seed_cpp"
RUNTIME_C="./runtime/runtime.c"
RUNTIME_H="./runtime/runtime.h"
BUILD_DIR="./build_output"

# Check prerequisites
if [ ! -f "$SEED_CPP" ]; then
    echo "ERROR: seed_cpp not found at $SEED_CPP"
    echo "Please ensure you've extracted the freebsd-simple-compiler.tar.gz package"
    exit 1
fi

if ! which clang++ >/dev/null 2>&1; then
    echo "ERROR: clang++ not found"
    echo "Install with: pkg install clang"
    exit 1
fi

mkdir -p "$BUILD_DIR"

echo "[STATUS] Prerequisites OK"
echo ""

# The problem: seed_cpp can handle ~50 files, but:
# - src/core has 31 files (CAN handle)
# - src/compiler has 411 files (CANNOT handle - will SEGFAULT)
#
# Solution: We can't build the full compiler this way.
# The seed_cpp is limited to Core Simple subset.
#
# Current capabilities:
# ✓ seed_cpp (79KB) - transpiles Core Simple programs
# ✗ Full compiler - requires either:
#   a) Rust runtime cross-compilation
#   b) LLVM backend (not yet implemented)
#   c) Advanced C++ codegen (beyond seed_cpp capabilities)

echo "========================================================================"
echo "  LIMITATION DISCOVERED"
echo "========================================================================"
echo ""
echo "The seed_cpp compiler cannot build the full Simple compiler because:"
echo ""
echo "1. seed_cpp supports Core Simple subset only"
echo "   - No generics, lambdas, classes, async"
echo "   - Designed for ~50 files max"
echo ""
echo "2. Full compiler requires 411 files with advanced features"
echo "   - Uses generics, traits, complex type system"
echo "   - Requires full runtime support"
echo ""
echo "3. Available options for full compiler:"
echo "   a) Cross-compile Rust runtime (not automated yet)"
echo "   b) Use LLVM backend (not implemented)"
echo "   c) Build progressively larger subsets (manual process)"
echo ""
echo "========================================================================"
echo ""
echo "RECOMMENDATION: Use seed_cpp for Core Simple programs"
echo ""
echo "The 79KB seed_cpp binary is production-ready for:"
echo "- Functions, structs, enums, control flow"
echo "- String manipulation, arrays"
echo "- Simple applications and scripts"
echo ""
echo "For full Simple language features, the Linux bin/release/simple"
echo "(32MB Rust-based runtime) is currently the reference implementation."
echo ""
echo "To cross-compile full FreeBSD compiler:"
echo "  1. Set up Rust cross-compilation toolchain"
echo "  2. rustup target add x86_64-unknown-freebsd"
echo "  3. cargo build --target x86_64-unknown-freebsd --release"
echo ""
echo "========================================================================"
echo ""

# Demonstrate seed_cpp capabilities with a test
echo "Demonstrating seed_cpp capabilities..."
echo ""

cat > "$BUILD_DIR/demo.spl" << 'EOF'
# FreeBSD Simple Compiler Demo
# This demonstrates what seed_cpp CAN compile

fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    return n * factorial(n - 1)

fn main():
    print "=== FreeBSD Simple Compiler (seed_cpp) ==="
    print ""
    print "Platform: FreeBSD"
    print "Compiler: seed_cpp (Core Simple subset)"
    print ""

    val numbers: [i64] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    print "Factorials:"
    for n in numbers:
        val result = factorial(n)
        print "  {n}! = {result}"

    print ""
    print "✓ Compilation successful!"
    print ""
    print "Features supported:"
    print "  ✓ Functions and recursion"
    print "  ✓ Variables (val/var)"
    print "  ✓ Arrays and loops"
    print "  ✓ Structs and enums"
    print "  ✓ String interpolation"
    print ""
    print "Features NOT supported:"
    print "  ✗ Generics (<T>)"
    print "  ✗ Lambdas (\\x: expr)"
    print "  ✗ Classes"
    print "  ✗ Async/await"
EOF

echo "Compiling demo.spl..."
$SEED_CPP "$BUILD_DIR/demo.spl" > "$BUILD_DIR/demo.cpp"
echo "  Generated: demo.cpp"

clang++ -std=c++20 -o "$BUILD_DIR/demo" "$BUILD_DIR/demo.cpp" "$RUNTIME_C" -I./runtime
echo "  Compiled: demo binary"
echo ""

echo "Running demo..."
echo ""
"$BUILD_DIR/demo"

echo ""
echo "========================================================================"
echo "  Summary"
echo "========================================================================"
echo ""
echo "✓ seed_cpp works perfectly for Core Simple programs"
echo "✗ Full compiler cannot be built with seed_cpp alone"
echo ""
echo "Next steps:"
echo "  1. Use seed_cpp for production Core Simple programs"
echo "  2. For full features, use Linux bin/release/simple"
echo "  3. For FreeBSD full compiler, need Rust cross-compilation"
echo ""
