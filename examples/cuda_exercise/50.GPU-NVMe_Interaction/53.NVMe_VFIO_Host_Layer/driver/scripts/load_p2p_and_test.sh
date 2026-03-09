#!/bin/bash

echo "============================================"
echo "P2P Driver Loading and Testing Script"
echo "============================================"
echo ""
echo "This script will:"
echo "1. Load the GPU P2P kernel modules"
echo "2. Run Mode 2-6 benchmarks with P2P enabled"
echo ""
echo "IMPORTANT: You need to run this with sudo:"
echo "  sudo ./load_p2p_and_test.sh"
echo ""

if [[ $EUID -ne 0 ]]; then
   echo "ERROR: This script must be run as root (use sudo)" 
   exit 1
fi

# Load the modules
echo "Loading P2P kernel modules..."
cd /home/ormastes/dev/pub/cuda_exercise/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/driver

# Load core module first
echo "Loading gpu_p2p_core.ko..."
insmod gpu_p2p_core/gpu_p2p_core.ko || echo "Core module may already be loaded"

# Load NVIDIA bridge module
echo "Loading gpu_p2p_nvidia.ko..."
insmod gpu_p2p_nvidia/gpu_p2p_nvidia.ko || echo "NVIDIA module may already be loaded"

# Check if modules loaded
echo ""
echo "Checking loaded modules..."
lsmod | grep gpu_p2p

# Check for device node
echo ""
echo "Checking for device node..."
ls -la /dev/gpu_p2p* 2>/dev/null || echo "No /dev/gpu_p2p device found"

# Now run the benchmarks
echo ""
echo "============================================"
echo "Running Mode 2-6 Benchmarks with P2P"
echo "============================================"
echo ""

cd /home/ormastes/dev/pub/cuda_exercise/build

export NVME_NSID="1"
export NVME_LBA_SIZE="512"
export NVME_SLBA="2000000"

# Test PM9A1 (DBC-capable)
echo "Testing PM9A1 (09:00.0) with P2P enabled"
echo "----------------------------------------"

echo "Mode 2:"
NVME_BDF="0000:09:00.0" timeout 15 ./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode2_host_daemon_gpu --gtest_filter="*Throughput*" 2>&1 | grep -A10 "Performance" || echo "FAILED/TIMEOUT"

echo ""
echo "Mode 3:"
NVME_BDF="0000:09:00.0" timeout 15 ./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode3_host_dbc_host --gtest_filter="*Throughput*" 2>&1 | grep -A10 "Performance" || echo "FAILED/TIMEOUT"

echo ""
echo "Mode 5 (GPU-Initiated):"
NVME_BDF="0000:09:00.0" timeout 15 ./50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode5_gpu_initiated_dbc --gtest_filter="*GPU_Initiated*" 2>&1 | grep -A10 "Performance:" || echo "FAILED/TIMEOUT"

echo ""
echo "============================================"
echo "P2P Testing Complete"
echo "============================================"
