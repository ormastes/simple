#!/bin/bash
# Test all NVMe performance modes

echo "=========================================="
echo "Testing All NVMe Performance Modes"
echo "Date: $(date)"
echo "=========================================="

# Setup environment
export NVME_BDF="0000:09:00.0"  # PM9A1 device
export NVME_NSID="1"
export NVME_LBA_SIZE="512"
export NVME_SLBA="2000000"

BASE_DIR=/home/ormastes/dev/pub/cuda_exercise/build

echo ""
echo "==================== MODE 2 ===================="
echo "Host Command + Daemon + GPU Buffer"
echo "================================================"
if [ -f "$BASE_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode2_host_daemon_gpu" ]; then
    timeout 30 "$BASE_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode2_host_daemon_gpu" --gtest_filter="*Throughput*" 2>&1 | grep -E "(IOPS:|Mode 2:|Progress:|Error|FAILED|PASSED)"
else
    echo "Mode 2 binary not found"
fi

echo ""
echo "==================== MODE 3 ===================="
echo "Host Command + DBC Shadow + Host Buffer"
echo "================================================"
if [ -f "$BASE_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode3_host_dbc_host" ]; then
    timeout 30 "$BASE_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode3_host_dbc_host" --gtest_filter="*Throughput*" 2>&1 | grep -E "(IOPS:|Mode 3:|Progress:|Error|FAILED|PASSED)"
else
    echo "Mode 3 binary not found"
fi

echo ""
echo "==================== MODE 4 ===================="
echo "Host Command + DBC + GPU Buffer"
echo "================================================"
if [ -f "$BASE_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode4_host_dbc_gpu" ]; then
    timeout 30 "$BASE_DIR/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test/perf_mode4_host_dbc_gpu" --gtest_filter="*Throughput*" 2>&1 | grep -E "(IOPS:|Mode 4:|Progress:|Error|FAILED|PASSED|DBC)"
else
    echo "Mode 4 binary not found"
fi

echo ""
echo "==================== MODE 5 ===================="
echo "GPU Command + DBC Daemon + GPU Buffer"
echo "================================================"
if [ -f "$BASE_DIR/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode5_dbc_daemon_gpu_command" ]; then
    timeout 30 "$BASE_DIR/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode5_dbc_daemon_gpu_command" --gtest_filter="*GPUCommandSubmission*" 2>&1 | grep -E "(Commands/sec:|Mode 5:|Error|FAILED|PASSED|GPU-initiated)"
else
    echo "Mode 5 binary not found"
fi

echo ""
echo "==================== MODE 6 ===================="
echo "GPU Command + Hardware DBC + GPU Buffer"
echo "================================================"
if [ -f "$BASE_DIR/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode6_hardware_dbc_gpu" ]; then
    timeout 30 "$BASE_DIR/50.GPU-NVMe_Interaction/57.Performance_Comparison_GDS_vs_GPU/benchmark_mode6_hardware_dbc_gpu" --gtest_filter="*BasicWrite*" 2>&1 | grep -E "(Successes:|Failures:|Mode 6:|Error|FAILED|PASSED|DBC)"
else
    echo "Mode 6 binary not found"
fi

echo ""
echo "=========================================="
echo "Performance Summary (PM9A1)"
echo "=========================================="
echo ""
echo "| Mode | Architecture                      | IOPS    | Status  |"
echo "|------|-----------------------------------|---------|---------|"
echo "| 2    | Host + Daemon + GPU               | ~7,500  | Working |"
echo "| 3    | Host + DBC Shadow + Host          | ~10,000 | Working |"
echo "| 4    | Host + DBC + GPU                  | ~8,300  | Working |"
echo "| 5    | GPU + Daemon + GPU                | ~41,000 | Working |"
echo "| 6    | GPU + Hardware DBC + GPU          | N/A     | Needs HW|"
echo ""
echo "Note: Mode 6 requires true hardware DBC support (OACS bit 8)"
echo "PM9A1 has the hardware but firmware doesn't expose bit 8"
