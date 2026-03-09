#!/usr/bin/env bash
# check_gds_setup.sh - Verify GPUDirect Storage configuration
#
# Usage: ./check_gds_setup.sh
#
# Description:
#   This script checks if GPUDirect Storage is properly configured
#   on the system. It verifies driver installation, kernel modules,
#   and runs gdscheck if available.

set -euo pipefail

echo "================================================"
echo "GPUDirect Storage Configuration Check"
echo "================================================"
echo ""

# Check CUDA installation
echo "[1/6] Checking CUDA installation..."
if command -v nvcc &> /dev/null; then
    CUDA_VERSION=$(nvcc --version | grep "release" | awk '{print $5}' | sed 's/,//')
    echo "  ✓ CUDA Toolkit version: $CUDA_VERSION"
else
    echo "  ✗ CUDA Toolkit not found"
    exit 1
fi
echo ""

# Check GPU availability
echo "[2/6] Checking GPU availability..."
if command -v nvidia-smi &> /dev/null; then
    GPU_COUNT=$(nvidia-smi --query-gpu=name --format=csv,noheader | wc -l)
    echo "  ✓ Found $GPU_COUNT GPU(s):"
    nvidia-smi --query-gpu=name,compute_cap --format=csv,noheader | sed 's/^/    /'
else
    echo "  ✗ nvidia-smi not found"
    exit 1
fi
echo ""

# Check nvidia-fs module (optional for CUDA 12.8+)
echo "[3/6] Checking nvidia-fs kernel module..."
if lsmod | grep -q nvidia_fs; then
    NVIDIA_FS_VERSION=$(cat /proc/driver/nvidia-fs/version 2>/dev/null || echo "unknown")
    echo "  ✓ nvidia-fs module loaded (version: $NVIDIA_FS_VERSION)"
else
    echo "  ⚠ nvidia-fs module not loaded"
    echo "    (This is OK if using CUDA 12.8+ with upstream P2P support)"
fi
echo ""

# Check kernel P2P support
echo "[4/6] Checking kernel PCIe P2P support..."
if [ -f /sys/module/nvme_core/parameters/p2pdma_enabled ]; then
    P2P_STATUS=$(cat /sys/module/nvme_core/parameters/p2pdma_enabled)
    if [ "$P2P_STATUS" = "Y" ] || [ "$P2P_STATUS" = "1" ]; then
        echo "  ✓ NVMe P2P DMA enabled"
    else
        echo "  ⚠ NVMe P2P DMA disabled"
    fi
else
    echo "  ⚠ Cannot determine P2P status"
fi
echo ""

# Check cuFile library
echo "[5/6] Checking cuFile library..."
CUFILE_PATHS=(
    "/usr/local/cuda/lib64/libcufile.so"
    "/usr/lib/x86_64-linux-gnu/libcufile.so"
)

CUFILE_FOUND=false
for path in "${CUFILE_PATHS[@]}"; do
    if [ -f "$path" ]; then
        echo "  ✓ cuFile library found: $path"
        CUFILE_FOUND=true
        break
    fi
done

if [ "$CUFILE_FOUND" = false ]; then
    echo "  ✗ cuFile library not found"
    echo "    Install with: sudo apt-get install libcufile-dev"
fi
echo ""

# Run gdscheck if available
echo "[6/6] Running gdscheck diagnostics..."
GDSCHECK_PATHS=(
    "/usr/local/cuda/gds/tools/gdscheck.py"
    "/usr/local/cuda-${CUDA_VERSION}/gds/tools/gdscheck.py"
)

GDSCHECK_FOUND=false
for path in "${GDSCHECK_PATHS[@]}"; do
    if [ -f "$path" ]; then
        echo "  Running: $path -p"
        echo ""
        python3 "$path" -p || true
        GDSCHECK_FOUND=true
        break
    fi
done

if [ "$GDSCHECK_FOUND" = false ]; then
    echo "  ⚠ gdscheck.py not found"
    echo "    (Install CUDA GDS tools for detailed diagnostics)"
fi
echo ""

echo "================================================"
echo "Configuration check complete"
echo "================================================"
