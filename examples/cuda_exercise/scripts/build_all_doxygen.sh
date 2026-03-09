#!/usr/bin/env bash
# build_all_doxygen.sh - Build Doxygen documentation for all modules 16+
#
# Usage: ./scripts/build_all_doxygen.sh [build_directory]
#
# Description:
#   Builds Doxygen documentation for all modules from 10-40 that have
#   doxygen directories (Module 16+). Generated HTML will be in
#   build/XX.Module_Name/doxygen/html/

set -euo pipefail

# Default build directory
BUILD_DIR="${1:-build}"
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$PROJECT_ROOT"

if [ ! -d "$BUILD_DIR" ]; then
    echo "Error: Build directory '$BUILD_DIR' does not exist"
    echo "Please run cmake first: cmake -B $BUILD_DIR -G Ninja"
    exit 1
fi

cd "$BUILD_DIR"

# Check if ninja/make is available
if command -v ninja &> /dev/null; then
    BUILD_CMD="ninja"
elif command -v make &> /dev/null; then
    BUILD_CMD="make"
else
    echo "Error: Neither ninja nor make found"
    exit 1
fi

echo "=========================================="
echo "Building Doxygen Documentation"
echo "=========================================="
echo "Build directory: $BUILD_DIR"
echo "Build command: $BUILD_CMD"
echo ""

# Doxygen targets for modules 10-40 (Module 16+)
DOXYGEN_TARGETS=(
    # 10.cuda_basic (16-19)
    "doxygen_16_Error_Handling_and_Debugging"
    "doxygen_17_Memory_Hierarchy"
    "doxygen_18_Thread_Hierarchy_Practice"
    "doxygen_19_CUDA_Memory_API"

    # 20.cuda_intermediate (21-27)
    "doxygen_21_Synchronization_and_Atomics"
    "doxygen_22_Streams_and_Async"
    "doxygen_23_Shared_Memory"
    "doxygen_24_Memory_Coalescing_and_Bank_Conflicts"
    "doxygen_25_Dynamic_Parallelism"
    "doxygen_26_Cooperative_Groups"
    "doxygen_27_Multi_GPU_Programming"

    # 30.CUDA_Libraries (31-38)
    "doxygen_31_cuBLAS"
    "doxygen_32_cuFFT"
    "doxygen_33_cuRAND"
    "doxygen_34_cuSPARSE"
    "doxygen_35_Thrust"
    "doxygen_36_cuDNN"
    "doxygen_37_GPUDirect_Storage"
    "doxygen_38_Tensor_Cores"

    # 40.cuda_advanced (41-49)
    "doxygen_41_Advanced_PTX_Assembly"
    "doxygen_42_Compiler_Optimizations"
    "doxygen_43_CUDA_Intrinsics"
    "doxygen_44_CUDA_Graphs"
    "doxygen_45_CUDA_IPC"
    "doxygen_46_Virtual_Memory"
    "doxygen_47_Hardware_Scheduling"
    "doxygen_48_Tile_Based_Programming"
    "doxygen_49_Zstd_Compression"
)

TOTAL=${#DOXYGEN_TARGETS[@]}
SUCCESS=0
FAILED=0
SKIPPED=0

echo "Total modules to document: $TOTAL"
echo ""

for target in "${DOXYGEN_TARGETS[@]}"; do
    echo "Building: $target"

    # Check if target exists
    if ! $BUILD_CMD -t "$target" &>/dev/null; then
        echo "  ⚠ SKIPPED (target not found)"
        ((SKIPPED++))
        continue
    fi

    # Build the target
    if $BUILD_CMD "$target" > /dev/null 2>&1; then
        echo "  ✓ SUCCESS"
        ((SUCCESS++))
    else
        echo "  ✗ FAILED"
        ((FAILED++))
    fi
done

echo ""
echo "=========================================="
echo "Documentation Build Summary"
echo "=========================================="
echo "Total modules: $TOTAL"
echo "Success: $SUCCESS"
echo "Failed: $FAILED"
echo "Skipped: $SKIPPED"
echo ""

if [ $FAILED -eq 0 ]; then
    echo "✓ All documentation built successfully!"
    echo ""
    echo "View documentation:"
    echo "  Open build/XX.Module_Name/doxygen/html/index.html in a browser"
    echo ""
    echo "Example:"
    echo "  xdg-open build/20.cuda_intermediate/23.Shared_Memory/doxygen/html/index.html"
    exit 0
else
    echo "✗ Some documentation builds failed"
    exit 1
fi
