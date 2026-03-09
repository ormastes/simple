# Module 53 Performance Tests
#
# These tests measure the performance of different NVMe I/O modes:
# - Mode 1: Host command + MMIO doorbell + Pinned host buffer
# - Mode 2: Host command + MMIO doorbell + GPU buffer (requires P2P)
# - Mode 3: Host command + DBC doorbell + Host buffer
#
# Each test reads 4KB chunks and processes them with GPU kernels
# to simulate realistic workloads.

message(STATUS "")
message(STATUS "=== Module 53 Performance Tests ===")

set(PERF_TEST_INCLUDES
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
    ${CMAKE_CURRENT_SOURCE_DIR}/../../src
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/00.perf_common/include
)

# ============================================================================
# Mode 1: Host + MMIO + Pinned Host Buffer
# ============================================================================

add_executable(perf_mode1_host_mmio_pinned
    mode1_host_mmio_pinned.cu
)

target_include_directories(perf_mode1_host_mmio_pinned PRIVATE
    ${PERF_TEST_INCLUDES}
)

target_link_libraries(perf_mode1_host_mmio_pinned PRIVATE
    mapping_host
    host_io_host_mem
    perf_common
    ${CUDA_BASIC_LIB}
    GTest::gtest
)

# Add profiling targets
add_profiling_targets(perf_mode1_host_mmio_pinned)

# Register with CTest
gtest_discover_tests(perf_mode1_host_mmio_pinned
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "performance;mode1;host_mmio"
)

# ============================================================================
# Mode 2: Host + Daemon (GPU Memory) + GPU Buffer
# ============================================================================

add_executable(perf_mode2_host_daemon_gpu
    mode2_host_daemon_gpu.cu
)

target_include_directories(perf_mode2_host_daemon_gpu PRIVATE
    ${PERF_TEST_INCLUDES}
)

target_link_libraries(perf_mode2_host_daemon_gpu PRIVATE
    mapping_host
    host_io_host_mem
    perf_common
    ${CUDA_BASIC_LIB}
    GTest::gtest
)

add_profiling_targets(perf_mode2_host_daemon_gpu)

gtest_discover_tests(perf_mode2_host_daemon_gpu
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "performance;mode2;daemon_gpu"
)

# ============================================================================
# Mode 3: Host + DBC Daemon + Host Buffer
# ============================================================================

add_executable(perf_mode3_host_dbc_host
    mode3_host_dbc_host.cu
)

target_include_directories(perf_mode3_host_dbc_host PRIVATE
    ${PERF_TEST_INCLUDES}
)

target_link_libraries(perf_mode3_host_dbc_host PRIVATE
    mapping_host
    host_io_host_mem
    perf_common
    ${CUDA_BASIC_LIB}
    GTest::gtest
)

add_profiling_targets(perf_mode3_host_dbc_host)

gtest_discover_tests(perf_mode3_host_dbc_host
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "performance;mode3;host_dbc"
)

# ============================================================================
# Mode 4: Host + DBC Hardware + GPU Buffer
# ============================================================================

add_executable(perf_mode4_host_dbc_gpu
    mode4_host_dbc_gpu.cu
)

target_include_directories(perf_mode4_host_dbc_gpu PRIVATE
    ${PERF_TEST_INCLUDES}
)

target_link_libraries(perf_mode4_host_dbc_gpu PRIVATE
    mapping_host
    host_io_host_mem
    device_detector
    dbc_setup
    mapping_gpu_55
    perf_common
    ${CUDA_BASIC_LIB}
    GTest::gtest
)

add_profiling_targets(perf_mode4_host_dbc_gpu)

gtest_discover_tests(perf_mode4_host_dbc_gpu
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "performance;mode4;dbc_hardware"
)

# ============================================================================
# Mode 0 (Baseline): Host + MMIO + Regular Host Buffer
# ============================================================================

add_executable(perf_mode0_baseline
    mode0_baseline.cu
)

target_include_directories(perf_mode0_baseline PRIVATE
    ${PERF_TEST_INCLUDES}
)

target_link_libraries(perf_mode0_baseline PRIVATE
    mapping_host
    host_io_host_mem
    perf_common
    ${CUDA_BASIC_LIB}
    GTest::gtest
)

add_profiling_targets(perf_mode0_baseline)

gtest_discover_tests(perf_mode0_baseline
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "performance;baseline;host_buffer"
)

# ============================================================================
# Mode 5: GPU-Initiated I/O with DBC (Most Advanced)
# ============================================================================

add_executable(perf_mode5_gpu_initiated_dbc
    mode5_gpu_initiated_dbc.cu
)

target_include_directories(perf_mode5_gpu_initiated_dbc PRIVATE
    ${PERF_TEST_INCLUDES}
)

target_link_libraries(perf_mode5_gpu_initiated_dbc PRIVATE
    mapping_host
    host_io_host_mem
    cuda_io_host_mem     # For CUDA pinned memory
    perf_common
    ${CUDA_BASIC_LIB}
    GTest::gtest
)

# Add profiling targets
add_profiling_targets(perf_mode5_gpu_initiated_dbc)

# Register with CTest
gtest_discover_tests(perf_mode5_gpu_initiated_dbc
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "performance;mode5;gpu_initiated;dbc"
)

message(STATUS "Performance Tests Configuration:")
message(STATUS "  Mode 0 (Baseline): Regular host buffer + memcpy")
message(STATUS "  Mode 1 (Pinned):   Pinned host buffer + fast memcpy")
message(STATUS "  Mode 2 (GPU P2P):  GPU buffer + direct DMA (requires P2P)")
message(STATUS "  Mode 5 (GPU Init): GPU-initiated I/O + DBC + GPU buffer 🚀")
message(STATUS "")
message(STATUS "Each test performs:")
message(STATUS "  - 1000 iterations of 4KB reads")
message(STATUS "  - GPU kernel processing after each read")
message(STATUS "  - Performance measurement breakdown")
message(STATUS "")
message(STATUS "To run performance tests:")
message(STATUS "  1. Set environment:")
message(STATUS "     export NVME_BDF=\"0000:41:00.0\"")
message(STATUS "     export NVME_NSID=\"1\"")
message(STATUS "     export NVME_LBA_SIZE=\"512\"")
message(STATUS "     export NVME_SLBA=\"2000000\"")
message(STATUS "")
message(STATUS "  2. Run individual mode:")
message(STATUS "     sudo -E ./perf_mode1_host_mmio_pinned")
message(STATUS "")
message(STATUS "Comparison harness is currently disabled; run individual mode binaries from the build tree.")
message(STATUS "")
