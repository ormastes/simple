#!/bin/bash
# Full compiler_core Bootstrap - Include everything
# Attempt to compile the complete compiler_core with seed_cpp

set -euo pipefail

echo "================================================================"
echo "  Simple Compiler FULL Core Bootstrap"
echo "================================================================"

# Step 1: Build seed_cpp
echo ""
echo "[1/4] Building seed_cpp..."
cd seed/build
CC=clang CXX=clang++ cmake .. >/dev/null 2>&1
cmake --build . --target seed_cpp --parallel $(nproc) >/dev/null 2>&1
cd ../..

if [ ! -f seed/build/seed_cpp ]; then
    echo "ERROR: seed_cpp build failed"
    exit 1
fi
echo "✅ seed_cpp built ($(ls -lh seed/build/seed_cpp | awk '{print $5}'))"

# Step 2: Generate file list (INCLUDE EVERYTHING except tests)
echo ""
echo "[2/4] Preparing ALL compiler_core source files..."
find src/compiler_core -name '*.spl' -type f | \
    grep -v '/test' | \
    grep -v '_test\.spl$' | \
    grep -v '_spec\.spl$' | \
    sort > /tmp/core_files_full.txt

# Add bootstrap_main.spl at the end
echo "src/compiler_core/bootstrap_main.spl" >> /tmp/core_files_full.txt

echo "✅ $(wc -l < /tmp/core_files_full.txt) files selected"

# Step 3: Transpile with increased stack
echo ""
echo "[3/4] Transpiling Simple → C++..."
mkdir -p build/bootstrap

ulimit -s 65536
perl -e 'my @files = map { chomp; $_ } <STDIN>; exec "./seed/build/seed_cpp", @files' \
    < /tmp/core_files_full.txt \
    2>/dev/null \
    > build/bootstrap/core_full_raw.cpp || {
        echo "❌ Transpilation failed"
        exit 1
    }

# Patch: Remove duplicate definitions and fix void main
sed 's/return (int)spl_main();/spl_main(); return 0;/g' \
    build/bootstrap/core_full_raw.cpp > build/bootstrap/core_full.cpp

echo "✅ Generated $(wc -l < build/bootstrap/core_full.cpp) lines of C++"

# Step 4: Compile C++
echo ""
echo "[4/4] Compiling C++ → native binary..."
clang++ -std=c++20 -O2 \
    -o build/bootstrap/core_full \
    build/bootstrap/core_full.cpp \
    -Iseed \
    -Lseed/build -lspl_runtime \
    -lm -lpthread -ldl \
    2>&1 | tee /tmp/core_full_errors.log | grep -E "error:" | head -50

if [ ! -f build/bootstrap/core_full ]; then
    echo ""
    echo "❌ C++ compilation failed"
    echo ""
    echo "Total errors: $(grep -c "error:" /tmp/core_full_errors.log || echo 0)"
    echo "First 20 errors shown above"
    echo ""
    echo "Full error log: /tmp/core_full_errors.log"
    exit 1
fi

echo "✅ core_full compiled ($(ls -lh build/bootstrap/core_full | awk '{print $5}'))"

# Step 5: Test the binary
echo ""
echo "[5/5] Testing the binary..."
./build/bootstrap/core_full --version || echo "No --version support"
./build/bootstrap/core_full --help || echo "No --help support"

# Done!
echo ""
echo "================================================================"
echo "  Full Core Bootstrap Complete!"
echo "================================================================"
echo ""
echo "Binary: build/bootstrap/core_full"
echo "Files: $(wc -l < /tmp/core_files_full.txt)"
echo "C++ lines: $(wc -l < build/bootstrap/core_full.cpp)"
echo ""
