#!/bin/bash
# Build script with all startup optimizations: LTO, PGO, strip
#
# Usage:
#   scripts/build-optimized.sh              # LTO + strip (default)
#   scripts/build-optimized.sh --pgo        # LTO + PGO + strip (2-pass build)
#   scripts/build-optimized.sh --static     # LTO + static + strip
#   scripts/build-optimized.sh --pgo --static  # All optimizations
#
# PGO (Profile-Guided Optimization) runs a 2-pass build:
#   Pass 1: Build instrumented binary, run representative workloads
#   Pass 2: Rebuild using collected profile data for 5-15% improvement

set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_DIR="$DIR/build"
SRC_DIR="$DIR/src/compiler_cpp"

USE_PGO=false
USE_STATIC=false

for arg in "$@"; do
    case "$arg" in
        --pgo) USE_PGO=true ;;
        --static) USE_STATIC=true ;;
    esac
done

CMAKE_OPTS="-DCMAKE_BUILD_TYPE=Release -DENABLE_LTO=ON"
CMAKE_OPTS="$CMAKE_OPTS -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++"

if [ "$USE_STATIC" = "true" ]; then
    CMAKE_OPTS="$CMAKE_OPTS -DENABLE_STATIC=ON"
fi

if [ "$USE_PGO" = "true" ]; then
    echo "=== PGO Pass 1: Building instrumented binary ==="
    PGO_DIR="$BUILD_DIR/pgo-profiles"
    mkdir -p "$PGO_DIR"

    cmake -B "$BUILD_DIR" -G Ninja $CMAKE_OPTS -DENABLE_PGO_GENERATE=ON -DPGO_PROFILE_DIR="$PGO_DIR" -S "$SRC_DIR"
    ninja -C "$BUILD_DIR" -j$(nproc)

    echo "=== PGO Pass 1: Running representative workloads ==="
    export SIMPLE_LIB="$DIR/src"
    export SIMPLE_VERSION=$(cat "$DIR/VERSION" 2>/dev/null || echo "unknown")

    # Workload 1: --help (cold start path)
    "$BUILD_DIR/simple" --help >/dev/null 2>&1 || true
    # Workload 2: compile command
    "$BUILD_DIR/simple" compile --help >/dev/null 2>&1 || true
    # Workload 3: version
    "$BUILD_DIR/simple" --version >/dev/null 2>&1 || true

    echo "=== PGO Pass 2: Rebuilding with profile data ==="
    # Merge profile data if using clang
    if command -v llvm-profdata >/dev/null 2>&1; then
        llvm-profdata merge -output="$PGO_DIR/default.profdata" "$PGO_DIR"/*.profraw 2>/dev/null || true
    fi

    cmake -B "$BUILD_DIR" -G Ninja $CMAKE_OPTS -DENABLE_PGO_GENERATE=OFF -DENABLE_PGO_USE=ON -DPGO_PROFILE_DIR="$PGO_DIR" -S "$SRC_DIR"
    ninja -C "$BUILD_DIR" -j$(nproc)

    # Clean up profile data
    rm -rf "$PGO_DIR"
else
    echo "=== Building with LTO + strip ==="
    cmake -B "$BUILD_DIR" -G Ninja $CMAKE_OPTS -S "$SRC_DIR"
    ninja -C "$BUILD_DIR" -j$(nproc)
fi

echo ""
echo "=== Build complete ==="
ls -lh "$BUILD_DIR/simple" "$BUILD_DIR/simple_codegen"
echo ""
echo "Binary: $BUILD_DIR/simple"
file "$BUILD_DIR/simple"
