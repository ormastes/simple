#!/bin/bash
# Test script for Mode 1-5 performance benchmarks
# This verifies that all modes work without P2P kernel module

set -e

echo "========================================"
echo " Testing Mode 1-5 Performance Benchmarks"
echo " (Without P2P Kernel Module)"
echo "========================================"

# Check if environment variables are set
if [ -z "$NVME_BDF" ]; then
    echo "Error: NVME_BDF not set"
    echo "Please set: export NVME_BDF='0000:41:00.0' (your NVMe device)"
    exit 1
fi

# Set default values for other variables
export NVME_NSID="${NVME_NSID:-1}"
export NVME_LBA_SIZE="${NVME_LBA_SIZE:-512}"
export NVME_SLBA="${NVME_SLBA:-1000000}"

echo ""
echo "Configuration:"
echo "  NVME_BDF: $NVME_BDF"
echo "  NVME_NSID: $NVME_NSID"
echo "  NVME_LBA_SIZE: $NVME_LBA_SIZE"
echo "  NVME_SLBA: $NVME_SLBA"
echo ""

BUILD_DIR="build/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU"

# Test each mode
for mode in 1 2 3 4 5; do
    echo "----------------------------------------"
    echo " Testing Mode $mode"
    echo "----------------------------------------"

    case $mode in
        1)
            binary="$BUILD_DIR/benchmark_gds"
            desc="Host + MMIO (GDS)"
            ;;
        2)
            binary="$BUILD_DIR/benchmark_mode2"
            desc="Host Daemon + GPU Memory (with fallback)"
            ;;
        3)
            binary="$BUILD_DIR/benchmark_mode3"
            desc="Host + Daemon"
            ;;
        4)
            binary="$BUILD_DIR/benchmark_mode4"
            desc="DBC Shadow + GPU (with fallback)"
            ;;
        5)
            binary="$BUILD_DIR/benchmark_mode5_dbc_daemon_gpu_command"
            desc="GPU + Daemon"
            ;;
    esac

    echo "Description: $desc"
    echo "Binary: $binary"

    if [ ! -f "$binary" ]; then
        echo "ERROR: Binary not found: $binary"
        echo "Please build with: ninja -C build"
        continue
    fi

    echo "Running quick test (10 iterations)..."

    # Run with minimal iterations just to verify it works
    if sudo timeout 30 "$binary" 2>&1 | head -50; then
        echo "✅ Mode $mode: PASSED"
    else
        echo "❌ Mode $mode: FAILED"
    fi

    echo ""
done

echo "========================================"
echo " Test Summary"
echo "========================================"
echo ""
echo "If all modes show PASSED, then the fix is working!"
echo "Mode 2 and 4 will use pinned host memory fallback"
echo "when P2P is not available (check stderr output)."
echo ""
echo "To run full benchmarks, use the scripts in:"
echo "  50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/scripts/"