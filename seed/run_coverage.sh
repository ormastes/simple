#!/bin/bash
# Simple Bootstrap C/C++ Coverage Report
#
# Usage:
#   bash seed/run_coverage.sh
#
# Requirements: clang, clang++, llvm-profdata[-N], llvm-cov[-N]
# Output: seed/.build-coverage/report/ (HTML), summary to stdout

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUILD_DIR="$SCRIPT_DIR/.build-coverage"
PROFRAW_DIR="$BUILD_DIR/profraw"
REPORT_DIR="$BUILD_DIR/report"

# Find matching llvm tools for the clang version
CLANG_VER=$(clang --version | head -1 | grep -oP '\d+' | head -1)
if command -v "llvm-profdata-${CLANG_VER}" &>/dev/null; then
    PROFDATA="llvm-profdata-${CLANG_VER}"
    COV="llvm-cov-${CLANG_VER}"
elif command -v llvm-profdata &>/dev/null; then
    PROFDATA=llvm-profdata
    COV=llvm-cov
else
    echo "Error: llvm-profdata not found"; exit 1
fi
echo "Using: clang ${CLANG_VER}, $PROFDATA, $COV"

# Clean previous run
rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR" "$PROFRAW_DIR" "$REPORT_DIR"

echo "=== Building with LLVM coverage ==="
cd "$BUILD_DIR"
cmake "$SCRIPT_DIR" -DCOVERAGE=ON \
    -DCMAKE_C_COMPILER=clang \
    -DCMAKE_CXX_COMPILER=clang++ \
    -DCMAKE_BUILD_TYPE=Debug 2>&1 | grep -v "^--" || true

cmake --build . --parallel 2>&1

echo ""
echo "=== Running tests ==="

echo "--- runtime_test ---"
LLVM_PROFILE_FILE="$PROFRAW_DIR/runtime.profraw" ./runtime_test
echo ""

echo "--- c_runtime_test ---"
LLVM_PROFILE_FILE="$PROFRAW_DIR/c_runtime.profraw" ./c_runtime_test
echo ""

echo "--- seed_test ---"
echo "" | SEED_CPP="$(pwd)/seed_cpp" LLVM_PROFILE_FILE="$PROFRAW_DIR/seed_test_%p.profraw" ./seed_test
echo ""

# Run seed_cpp on all core .spl files for deeper coverage
echo "--- seed_cpp on core .spl files ---"
for f in "$SCRIPT_DIR"/../src/core/*.spl; do
    base=$(basename "$f" .spl)
    LLVM_PROFILE_FILE="$PROFRAW_DIR/seed_${base}.profraw" ./seed_cpp "$f" > /dev/null 2>&1 || true
done
echo "  compiled $(ls "$SCRIPT_DIR"/../src/core/*.spl | wc -l) files"
echo ""

echo "=== Merging profile data ==="
$PROFDATA merge -sparse "$PROFRAW_DIR"/*.profraw -o "$BUILD_DIR/merged.profdata"

echo "=== Coverage Report ==="
BINS="-object ./runtime_test -object ./c_runtime_test -object ./seed_cpp"

$COV report $BINS \
    -instr-profile="$BUILD_DIR/merged.profdata" \
    --sources "$SCRIPT_DIR/runtime.c" \
    --sources "$SCRIPT_DIR/seed.cpp" \
    --sources "$SCRIPT_DIR/../src/app/compile/c_runtime.c" \
    2>/dev/null || true

# HTML report
$COV show $BINS \
    -instr-profile="$BUILD_DIR/merged.profdata" \
    --sources "$SCRIPT_DIR/runtime.c" \
    --sources "$SCRIPT_DIR/seed.cpp" \
    --sources "$SCRIPT_DIR/../src/app/compile/c_runtime.c" \
    -format=html \
    -output-dir="$REPORT_DIR" \
    2>/dev/null || true

echo ""
echo "=== HTML report: $REPORT_DIR/index.html ==="
