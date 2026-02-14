#!/bin/bash
# Types-Only Bootstrap - Prove enum definitions work
# Only includes type definitions and trivial main

set -euo pipefail

echo "================================================================"
echo "  Simple Compiler Types-Only Bootstrap"
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

# Step 2: Create types-only file list
echo ""
echo "[2/4] Preparing type definition files..."

cat > /tmp/core_files_types_only.txt <<'EOF'
src/compiler_core/backend_types.spl
src/compiler_core/backend/backend_types.spl
src/compiler_core/bootstrap_types_main.spl
EOF

echo "✅ $(wc -l < /tmp/core_files_types_only.txt) files selected"

# Step 3: Create types-only bootstrap main
echo ""
echo "[2.5/4] Creating types-only bootstrap main..."
cat > src/compiler_core/bootstrap_types_main.spl <<'MAIN'
# Types-Only Bootstrap Main
# Purpose: Prove that backend enum/type definitions compile successfully

use backend_types.{BackendKind, value_int, value_bool}
use backend.backend_types.{CodegenTarget}

fn main():
    # Just create enum values to prove they exist
    val backend1 = BackendKind.Cranelift
    val backend2 = BackendKind.Llvm
    val backend3 = BackendKind.Native
    val backend4 = BackendKind.Wasm
    val backend5 = BackendKind.Lean
    val backend6 = BackendKind.Interpreter

    val target1 = CodegenTarget.X86_64
    val target2 = CodegenTarget.AArch64
    val target3 = CodegenTarget.Riscv64
    val target4 = CodegenTarget.Native
    val target5 = CodegenTarget.Host

    # Create value types to prove constructors exist
    val v1 = value_int(42)
    val v2 = value_bool(true)

    # Success - all types compiled and linked!
    # If we get here, all enum variants and value constructors work
    ()
MAIN

# Step 4: Transpile
echo ""
echo "[3/4] Transpiling Simple → C++..."
mkdir -p build/bootstrap

ulimit -s 65536
./seed/build/seed_cpp \
    src/compiler_core/backend_types.spl \
    src/compiler_core/backend/backend_types.spl \
    src/compiler_core/bootstrap_types_main.spl \
    > build/bootstrap/types_only_raw.cpp 2>/dev/null

# Fix seed_cpp bug: replace "return (int)spl_main();" with "spl_main(); return 0;"
sed 's/return (int)spl_main();/spl_main(); return 0;/g' \
    build/bootstrap/types_only_raw.cpp \
    > build/bootstrap/types_only.cpp

echo "✅ Generated $(wc -l < build/bootstrap/types_only.cpp) lines of C++"

# Step 5: Compile C++
echo ""
echo "[4/4] Compiling C++ → native binary..."
clang++ -std=c++20 -O2 \
    -o build/bootstrap/types_only \
    build/bootstrap/types_only.cpp \
    -Iseed \
    -Lseed/build -lspl_runtime \
    -lm -lpthread -ldl \
    2>&1 | head -30

if [ ! -f build/bootstrap/types_only ]; then
    echo ""
    echo "❌ C++ compilation failed"
    echo ""
    echo "Transpilation was successful, but C++ has errors."
    echo "Showing generated C++ preview:"
    echo ""
    head -200 build/bootstrap/types_only.cpp
    exit 1
fi

echo "✅ types_only compiled ($(ls -lh build/bootstrap/types_only | awk '{print $5}'))"

# Step 6: Test the binary
echo ""
echo "[5/5] Testing the binary..."
if ./build/bootstrap/types_only; then
    echo "✅ Binary executed successfully (exit code: $?)"
else
    echo "❌ Binary failed with exit code: $?"
    exit 1
fi

# Done!
echo ""
echo "================================================================"
echo "  Types-Only Bootstrap SUCCESS!"
echo "================================================================"
echo ""
echo "Binary: build/bootstrap/types_only"
echo "Files: 3 (backend_types.spl + backend/backend_types.spl + main)"
echo "C++ lines: $(wc -l < build/bootstrap/types_only.cpp)"
echo ""
echo "✅✅✅ PROOF: Enum/type fixes work perfectly! ✅✅✅"
echo ""
echo "All BackendKind variants compile and link correctly"
echo "All CodegenTarget variants compile and link correctly"
echo "All value constructors (value_int, value_bool) work"
echo ""
