cmake_minimum_required(VERSION 3.18)
project(57_Performance_Comparison_GDS_vs_GPU CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 57: Performance Comparison - GDS vs GPU-Initiated I/O
# Compares Module 55 (GDS: Host Queue + GPU Buffer) vs Module 56 (GPU Queue + GPU Buffer)
# Focus: Command submission overhead and end-to-end latency

# Define dummy profiling targets function if not available
if(NOT COMMAND add_profiling_targets)
    function(add_profiling_targets target)
        # Dummy implementation - profiling targets not available
    endfunction()
endif()

# Create library for shared kernel code
add_library(${MODULE}_kernels STATIC
    src/kernels/sum_kernel.cu
)

set_target_properties(${MODULE}_kernels PROPERTIES
    CUDA_ARCHITECTURES "${CMAKE_CUDA_ARCHITECTURES}"  # Inherit from parent (75=Turing, 80=Ampere, 86=Lovelace)
)

target_include_directories(${MODULE}_kernels PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/src
)

target_link_libraries(${MODULE}_kernels PUBLIC
    ${CUDA_BASIC_LIB}
)

# INTERFACE library to provide include paths
add_library(${MODULE}_lib INTERFACE)

target_include_directories(${MODULE}_lib INTERFACE
    ${CMAKE_CURRENT_SOURCE_DIR}/src
)

# Link against Module 53, 54, 55, and shared library targets
target_link_libraries(${MODULE}_lib INTERFACE
    nvme_vio_host               # Module 53: Host layer
    host_io_host_mem            # Module 53: Host memory I/O
    nvme_vio_cuda_host          # Module 54: CUDA host memory
    cuda_io_host_mem            # Module 54: Host memory allocations
    device_detector             # Module 53: NVMe/GPU capability detection
    nvme_vio_cuda_gpu_55        # Module 55: GPU memory I/O
    cuda_io_gpu_mem_55          # Module 55: GPU memory allocations
    perf_common                 # 00.perf_common: Shared performance testing utilities
    ${MODULE}_kernels
    ${CUDA_BASIC_LIB}
)

# ===== Benchmark Executables =====

# Mode 0: Host + MMIO + Regular (Pageable) Host Memory (BASELINE)
# Uses regular pageable memory - intentionally suboptimal for comparison
add_executable(benchmark_mode0_baseline
    test/benchmarks/mode0_not_pinned.cpp
)
target_include_directories(benchmark_mode0_baseline PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
)
target_link_libraries(benchmark_mode0_baseline PRIVATE ${MODULE}_lib)
add_profiling_targets(benchmark_mode0_baseline)
set_target_properties(benchmark_mode0_baseline PROPERTIES OUTPUT_NAME "benchmark_mode0")

# Mode 1: Host + MMIO + GDS/Pinned Memory
# Uses Module 56 P2P ioctl interface (kernels/gpu_p2p_ioctl.h)
add_executable(benchmark_mode1_gds
    test/benchmarks/mode1_pinned.cpp
)
target_include_directories(benchmark_mode1_gds PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test  # For helper/device_selection.h
)
target_link_libraries(benchmark_mode1_gds PRIVATE ${MODULE}_lib device_chooser)
add_profiling_targets(benchmark_mode1_gds)
set_target_properties(benchmark_mode1_gds PROPERTIES OUTPUT_NAME "benchmark_gds")

# Mode 2: Host + Daemon polling GPU Memory
add_executable(benchmark_mode2_host_daemon_gpu_mem
    test/benchmarks/mode2_dbc_daemon.cpp
)
target_include_directories(benchmark_mode2_host_daemon_gpu_mem PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
)
target_link_libraries(benchmark_mode2_host_daemon_gpu_mem PRIVATE ${MODULE}_lib)
add_profiling_targets(benchmark_mode2_host_daemon_gpu_mem)
# Set output name to match script expectations
set_target_properties(benchmark_mode2_host_daemon_gpu_mem PROPERTIES OUTPUT_NAME "benchmark_mode2")

# Mode 3: Host + Daemon + GPU Buffer
# NOTE: Mode 3 uses benchmark_host_dbc_daemon_real from Module 56, not this benchmark
# This benchmark_mode3_host_daemon is for fallback/alternative implementation (experimental)
add_executable(benchmark_mode3_host_daemon
    test/benchmarks/mode3_gpu_buffer.cpp
)
target_include_directories(benchmark_mode3_host_daemon PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
)
target_link_libraries(benchmark_mode3_host_daemon PRIVATE ${MODULE}_lib)
add_profiling_targets(benchmark_mode3_host_daemon)
# Set output name to match script expectations
set_target_properties(benchmark_mode3_host_daemon PROPERTIES OUTPUT_NAME "benchmark_mode3")

# Mode 4: DBC Shadow + GPU Queue/Buffer
add_executable(benchmark_mode3_gds_cufile
    test/benchmarks/mode3_1_gds_cufile.cpp
)
target_include_directories(benchmark_mode3_gds_cufile PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
)
target_link_libraries(benchmark_mode3_gds_cufile PRIVATE ${MODULE}_lib)
add_profiling_targets(benchmark_mode3_gds_cufile)
set_target_properties(benchmark_mode3_gds_cufile PROPERTIES OUTPUT_NAME "benchmark_mode3_gds_cufile")

add_executable(benchmark_mode4_dbc_shadow_gpu
    test/benchmarks/mode4_gpu_cmd_dbc_daemon.cu
)
target_include_directories(benchmark_mode4_dbc_shadow_gpu PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test  # For helper/device_selection.h
)
target_link_libraries(benchmark_mode4_dbc_shadow_gpu PRIVATE ${MODULE}_lib device_chooser dbc_setup)
set_target_properties(benchmark_mode4_dbc_shadow_gpu PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON
)
add_profiling_targets(benchmark_mode4_dbc_shadow_gpu)
# Set output name to match script expectations
set_target_properties(benchmark_mode4_dbc_shadow_gpu PROPERTIES OUTPUT_NAME "benchmark_mode4")

# Mode 5: DBC Daemon + GPU Command (TRUE GPU-INITIATED I/O)
# GPU builds commands, writes shadow doorbell, daemon propagates to MMIO
# This benchmark runs the entire loop in a SINGLE GPU kernel launch
add_executable(benchmark_mode5_dbc_daemon_gpu_command
    test/benchmarks/mode5_gpu_cq_dbc_daemon.cu
)
target_include_directories(benchmark_mode5_dbc_daemon_gpu_command PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test  # For helper/device_selection.h
)
target_link_libraries(benchmark_mode5_dbc_daemon_gpu_command PRIVATE
    ${MODULE}_lib
    device_chooser
    ${GTEST_BASIC_LIB}  # For GpuTest base class
)
set_target_properties(benchmark_mode5_dbc_daemon_gpu_command PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON
)
add_profiling_targets(benchmark_mode5_dbc_daemon_gpu_command)

# Mode 6: Hardware DBC + GPU Command (HARDWARE-POLLED SHADOW DOORBELL)
# GPU builds commands, writes shadow doorbell, NVMe hardware polls shadow buffer directly
# This requires DBC-capable NVMe controller (OACS bit 8 set)
add_executable(benchmark_mode6_hardware_dbc_gpu
    test/benchmarks/mode6_hw_dbc.cu
)
target_include_directories(benchmark_mode6_hardware_dbc_gpu PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/test
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/driver
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/test/performance_test
)
target_link_libraries(benchmark_mode6_hardware_dbc_gpu PRIVATE
    ${MODULE}_lib
    dbc_setup  # For nvme::allocate_shadow_doorbell_buffer
    device_chooser
    ${GTEST_BASIC_LIB}  # For GpuTest base class
)
set_target_properties(benchmark_mode6_hardware_dbc_gpu PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON
)
add_profiling_targets(benchmark_mode6_hardware_dbc_gpu)

# Mode 6 True Hardware DBC removed - use benchmark_mode6_hardware_dbc_gpu instead
# PM9A1 supports shadow doorbell with daemon polling (Mode 5-style operation)

# GPU-Initiated Benchmark (P2P utility) - REMOVED
# Use Mode 5 (benchmark_mode5_dbc_daemon_gpu_command) for GPU-initiated I/O testing

message(STATUS "Part 57: Performance Comparison - Mode 0-6 Benchmarks")
message(STATUS "  - benchmark_mode0_baseline: Mode 0 (Host + MMIO + Pageable) - BASELINE")
message(STATUS "  - benchmark_mode1_gds: Mode 1 (Host + MMIO + GDS)")
message(STATUS "  - benchmark_mode2_host_daemon_gpu_mem: Mode 2 (Host Daemon + GPU Memory)")
message(STATUS "  - benchmark_mode3_host_daemon: Mode 3 (Host + Daemon + GPU Buffer)")
message(STATUS "  - benchmark_mode4_dbc_shadow_gpu: Mode 4 (DBC Shadow + GPU)")
message(STATUS "  - benchmark_mode5_dbc_daemon_gpu_command: Mode 5 (GPU Command + Daemon) - SOFTWARE DBC")
message(STATUS "  - benchmark_mode6_hardware_dbc_gpu: Mode 6 (GPU Command + Hardware DBC) - HARDWARE DBC")
message(STATUS "  - Use run_comparison.sh to run all and compare results")

# ---- Doxygen documentation target ----
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in
)
