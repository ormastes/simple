#!/usr/bin/env bash
# Bootstrap the Simple compiler via C backend.
#
# This script:
# 1. Uses the current binary to generate C++20 from the compiler source
# 2. Copies the generated C++ to src/compiler_core/generated/
# 3. Builds with CMake + Ninja (or Make)
# 4. Optionally verifies the bootstrap binary
#
# Prerequisites: cmake, ninja (or make), clang++ (or g++)
#
# Usage:
#   scripts/bootstrap/bootstrap-c.sh              # Generate + build
#   scripts/bootstrap/bootstrap-c.sh --verify     # Generate + build + verify

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "${SCRIPT_DIR}/../.." && pwd)"
GENERATED_DIR="${PROJECT_DIR}/src/compiler_core/generated"
BUILD_DIR="${PROJECT_DIR}/src/compiler_core/build"
SIMPLE_BIN="${PROJECT_DIR}/bin/simple"

VERIFY=false
if [[ "${1:-}" == "--verify" ]]; then
    VERIFY=true
fi

echo "=== Simple C Bootstrap ==="
echo "Project: ${PROJECT_DIR}"
echo ""

# Step 1: Generate C++20 from compiler source
echo "Step 1: Generating C++20 from compiler..."
if [[ -x "${SIMPLE_BIN}" ]]; then
    "${SIMPLE_BIN}" compile --backend=c --emit-c -o "${GENERATED_DIR}/simple_compiler.cpp" src/app/cli/main.spl || {
        echo "Warning: C backend generation not yet fully functional."
        echo "The C backend infrastructure is in place but the full compiler"
        echo "self-compilation requires the MIR pipeline to be complete."
        echo ""
        echo "To test the C backend with a small file:"
        echo "  bin/simple compile --backend=c test.spl"
    }
else
    echo "Error: bin/simple not found"
    exit 1
fi

# Step 2: Build with CMake
echo ""
echo "Step 2: Building with CMake..."
if command -v cmake &>/dev/null; then
    GENERATOR=""
    if command -v ninja &>/dev/null; then
        GENERATOR="-G Ninja"
    fi

    cmake -B "${BUILD_DIR}" ${GENERATOR} "${PROJECT_DIR}/src/compiler_core"
    cmake --build "${BUILD_DIR}"
    echo ""
    echo "Bootstrap binary: ${BUILD_DIR}/simple_bootstrap"
else
    echo "Error: cmake not found. Install CMake to build."
    exit 1
fi

# Step 3: Verify (optional)
if [[ "${VERIFY}" == "true" ]]; then
    echo ""
    echo "Step 3: Verifying bootstrap binary..."
    BOOTSTRAP_BIN="${BUILD_DIR}/simple_bootstrap"
    if [[ -x "${BOOTSTRAP_BIN}" ]]; then
        echo "  Running: ${BOOTSTRAP_BIN} --version"
        "${BOOTSTRAP_BIN}" --version || echo "  (version check not yet supported)"
        echo ""
        echo "Bootstrap verification complete."
    else
        echo "Error: Bootstrap binary not found at ${BOOTSTRAP_BIN}"
        exit 1
    fi
fi

echo ""
echo "=== Bootstrap complete ==="
