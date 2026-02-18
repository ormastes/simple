#!/bin/bash
# Fixed Bootstrap Script - Pure Simple Path
# Uses seed_cpp with all discovered fixes applied

set -euo pipefail

echo "================================================================"
echo "  Simple Compiler Bootstrap (Fixed seed_cpp Path)"
echo "================================================================"

# Step 1: Build seed_cpp with fixes
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

# Step 2: Generate file list (exclude tests and problematic files)
echo ""
echo "[2/4] Preparing source files..."
find src/compiler -name '*.spl' -type f | \
    grep -v '/test_' | \
    grep -v '_test\.spl$' | \
    grep -v 'codegen\.spl$' | \
    grep -v '_phase[0-9]' | \
    grep -v 'exhaustiveness_validator\.spl$' | \
    grep -v 'link_wrapper\.spl$' | \
    grep -v '^src/compiler/effects' | \
    grep -v '^src/compiler/trait' | \
    grep -v '^src/compiler/bidir' | \
    grep -v '^src/compiler/const_keys' | \
    grep -v '^src/compiler/higher_rank' | \
    grep -v '^src/compiler/macro_checker' | \
    grep -v '^src/compiler/simd' | \
    grep -v '^src/compiler/variance' | \
    grep -v '^src/compiler/monomorphize' | \
    grep -v '^src/compiler/module_resolver' | \
    grep -v '/main\.spl$' | \
    grep -v 'config\.spl$' | \
    grep -v 'aop' | \
    sort > /tmp/core_files_bootstrap_tmp.txt

# Put config.spl first (defines Logger and other types used by AOP)
echo "src/compiler/config.spl" > /tmp/core_files_bootstrap.txt

# Add AOP files after config (they depend on Logger from config)
find src/compiler -name '*aop*.spl' -type f | sort >> /tmp/core_files_bootstrap.txt

# Add rest of files
cat /tmp/core_files_bootstrap_tmp.txt >> /tmp/core_files_bootstrap.txt

# Add bootstrap_main.spl at the end (must come after dependencies)
echo "src/compiler/bootstrap_main.spl" >> /tmp/core_files_bootstrap.txt

echo "✅ $(wc -l < /tmp/core_files_bootstrap.txt) files selected"

# Step 3: Transpile with increased stack
echo ""
echo "[3/4] Transpiling Simple → C++ (this takes ~5 seconds)..."
mkdir -p build/bootstrap

ulimit -s 65536  # Critical: Increase stack from 8MB to 64MB
perl -e 'my @files = map { chomp; $_ } <STDIN>; exec "./seed/build/seed_cpp", @files' \
    < /tmp/core_files_bootstrap.txt \
    2>/dev/null \
    > build/bootstrap/core1_raw.cpp

# Patch: Remove duplicate CodegenTarget_val definition (line with "= 12")
sed '/CodegenTarget_val = 12/d' build/bootstrap/core1_raw.cpp > build/bootstrap/core1.cpp

echo "✅ Generated $(wc -l < build/bootstrap/core1.cpp) lines of C++"

# Step 4: Compile C++ to native binary
echo ""
echo "[4/4] Compiling C++ → native binary..."
clang++ -std=c++20 -O2 \
    -o build/bootstrap/core1 \
    build/bootstrap/core1.cpp \
    -Iseed \
    -Lseed/build -lspl_runtime \
    -lm -lpthread -ldl \
    2>&1 | grep -v "warning:" || true

if [ ! -f build/bootstrap/core1 ]; then
    echo "ERROR: C++ compilation failed"
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
echo "Next steps:"
echo "  ./build/bootstrap/core1             # Run core compiler"
echo "  # Use core1 to compile full compiler (if memory permits)"
echo ""
