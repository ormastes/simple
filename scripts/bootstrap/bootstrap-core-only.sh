#!/bin/bash
# Core-Only Bootstrap - Exclude complex backend/linker code
set -euo pipefail

echo "================================================================"
echo "  Simple Compiler Core-Only Bootstrap"
echo "================================================================"

echo ""
echo "[1/4] Building seed_cpp..."
cd seed/build
CC=clang CXX=clang++ cmake .. >/dev/null 2>&1
cmake --build . --target seed_cpp --parallel $(nproc) 2>&1 | grep -E "Built target|error" || true
cd ../..

if [ ! -f seed/build/seed_cpp ]; then
    echo "ERROR: seed_cpp build failed"
    exit 1
fi
echo "✅ seed_cpp built"

echo ""
echo "[2/4] Preparing source files (CORE ONLY)..."
find src/compiler -name '*.spl' -type f | \
    grep -v '/test' | \
    grep -v '_test\.spl$' | \
    grep -v '_spec\.spl$' | \
    grep -v '_phase[0-9]' | \
    grep -v 'associated_types' | \
    grep -v '^src/compiler/aop' | \
    grep -v '^src/compiler/arch_rules' | \
    grep -v '^src/compiler/async' | \
    grep -v '^src/compiler/borrow' | \
    grep -v '^src/compiler/backend' | \
    grep -v '^src/compiler/linker' | \
    grep -v '^src/compiler/loader' | \
    grep -v '^src/compiler/effects' | \
    grep -v '^src/compiler/trait' | \
    grep -v '/main\.spl$' | \
    sort > /tmp/core_files_only.txt

echo "src/compiler/bootstrap_main.spl" >> /tmp/core_files_only.txt

echo "✅ $(wc -l < /tmp/core_files_only.txt) files selected"

echo ""
echo "[3/4] Transpiling Simple → C++..."
mkdir -p build/bootstrap

ulimit -s 65536
perl -e 'my @files = map { chomp; $_ } <STDIN>; exec "./seed/build/seed_cpp", @files' \
    < /tmp/core_files_only.txt \
    2>/dev/null \
    > build/bootstrap/core_only.cpp

echo "✅ Generated $(wc -l < build/bootstrap/core_only.cpp) lines of C++"

echo ""
echo "[4/4] Compiling C++ → native binary..."
clang++ -std=c++20 -O2 \
    -o build/bootstrap/core_only \
    build/bootstrap/core_only.cpp \
    -Iseed \
    -Lseed/build -lspl_runtime \
    -lm -lpthread -ldl \
    2>&1 | grep -E "error:" | head -30 || echo "✅ Compiled successfully!"

if [ -f build/bootstrap/core_only ]; then
    echo "✅ core_only binary: $(ls -lh build/bootstrap/core_only | awk '{print $5}')"
    echo ""
    echo "Running test:"
    ./build/bootstrap/core_only
else
    echo "❌ Compilation failed"
    exit 1
fi
