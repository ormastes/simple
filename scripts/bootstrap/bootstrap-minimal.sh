#!/bin/bash
# Minimal Bootstrap Script - Exclude problematic files
# Builds only files that seed_cpp can handle

set -euo pipefail

echo "================================================================"
echo "  Simple Compiler Minimal Bootstrap"
echo "================================================================"

# Step 1: Build seed_cpp
echo ""
echo "[1/4] Building seed_cpp..."
cd seed/build
rm -f CMakeCache.txt
CC=clang CXX=clang++ cmake .. >/dev/null
cmake --build . --target seed_cpp --parallel $(nproc) 2>&1 | grep -E "Built target|error" || true
cd ../..

if [ ! -f seed/build/seed_cpp ]; then
    echo "ERROR: seed_cpp build failed"
    exit 1
fi
echo "✅ seed_cpp built ($(ls -lh seed/build/seed_cpp | awk '{print $5}'))"

# Step 2: Generate file list (EXCLUDE problematic files)
echo ""
echo "[2/4] Preparing source files..."
find src/compiler_core -name '*.spl' -type f | \
    grep -v '/test' | \
    grep -v '_test\.spl$' | \
    grep -v '_spec\.spl$' | \
    grep -v '_phase[0-9]' | \
    grep -v 'associated_types' | \
    grep -v '^src/compiler_core/aop' | \
    grep -v '^src/compiler_core/arch_rules' | \
    grep -v '^src/compiler_core/async_integration' | \
    grep -v '^src/compiler_core/borrow_check' | \
    grep -v '^src/compiler_core/effects' | \
    grep -v '^src/compiler_core/trait' | \
    grep -v '^src/compiler_core/bidir' | \
    grep -v '^src/compiler_core/const_keys' | \
    grep -v '^src/compiler_core/higher_rank' | \
    grep -v '^src/compiler_core/macro_checker' | \
    grep -v '^src/compiler_core/simd' | \
    grep -v '^src/compiler_core/variance' | \
    grep -v '^src/compiler_core/monomorphize' | \
    grep -v '^src/compiler_core/module_resolver' | \
    grep -v '^src/compiler_core/backend/lean_borrow' | \
    grep -v '^src/compiler_core/linker' | \
    grep -v '^src/compiler_core/blocks' | \
    grep -v '^src/compiler_core/codegen' | \
    grep -v '^src/compiler_core/backend/llvm_backend' | \
    grep -v '^src/compiler_core/backend/sdn' | \
    grep -v '^src/compiler_core/backend/cuda_backend' | \
    grep -v '^src/compiler_core/backend/vulkan_backend' | \
    grep -v 'bitfield\.spl$' | \
    grep -v 'init\.spl$' | \
    grep -v 'predicate_parser\.spl$' | \
    grep -v '/main\.spl$' | \
    sort > /tmp/core_files_minimal_bs.txt

# Add bootstrap_main.spl at the end
echo "src/compiler_core/bootstrap_main.spl" >> /tmp/core_files_minimal_bs.txt

echo "✅ $(wc -l < /tmp/core_files_minimal_bs.txt) files selected"

# Step 3: Transpile with increased stack
echo ""
echo "[3/4] Transpiling Simple → C++..."
mkdir -p build/bootstrap

ulimit -s 65536
perl -e 'my @files = map { chomp; $_ } <STDIN>; exec "./seed/build/seed_cpp", @files' \
    < /tmp/core_files_minimal_bs.txt \
    2>/dev/null \
    > build/bootstrap/core1_raw.cpp

# Patch: Remove duplicate definitions
sed '/CodegenTarget_val = 12/d' build/bootstrap/core1_raw.cpp > build/bootstrap/core1.cpp

echo "✅ Generated $(wc -l < build/bootstrap/core1.cpp) lines of C++"

# Step 4: Compile C++
echo ""
echo "[4/4] Compiling C++ → native binary..."
clang++ -std=c++20 -O2 \
    -o build/bootstrap/core1 \
    build/bootstrap/core1.cpp \
    -Iseed \
    -Lseed/build -lspl_runtime \
    -lm -lpthread -ldl \
    2>&1 | grep -E "error:" | head -20 || true

if [ ! -f build/bootstrap/core1 ]; then
    echo "❌ C++ compilation failed (showing first 20 errors above)"
    echo ""
    echo "Showing problematic C++ code context:"
    grep -n "error:" build/bootstrap/core1.cpp 2>/dev/null | head -5 || true
    exit 1
fi

echo "✅ core1 compiled ($(ls -lh build/bootstrap/core1 | awk '{print $5}'))"

# Done!
echo ""
echo "================================================================"
echo "  Bootstrap Complete!"
echo "================================================================"
echo ""
echo "Core compiler: build/bootstrap/core1"
echo ""
