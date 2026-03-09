# Module 53 System Tests
#
# System-level tests that exercise the complete I/O path with real hardware.
# These tests require:
# - Real NVMe device accessible via VFIO
# - Proper environment variable configuration
# - Root/sudo privileges for VFIO operations

add_executable(test_host_io_system
    53_test_host_io_system.cpp
)

target_include_directories(test_host_io_system PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_host_io_system PRIVATE
    device_detector
    device_detector
    setup_helper
    system_test_config
    mapping_host
    host_io_host_mem
    nvme_patterns        # Migrated from pattern_helper
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

# Add profiling targets
add_profiling_targets(test_host_io_system)

# Register with CTest
gtest_discover_tests(test_host_io_system
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "system;hardware;vfio;setup_helper"
)

# ============================================================================
# Module 53: Page Size Configuration System Tests
# ============================================================================

add_executable(test_page_size_config_system
    53_test_page_size_config_system.cpp
)

target_include_directories(test_page_size_config_system PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_page_size_config_system PRIVATE
    device_detector
    setup_helper
    system_test_config
    mapping_host
    host_io_host_mem
    nvme_patterns
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gtest_main
    GTest::gmock
)

# Add profiling targets
add_profiling_targets(test_page_size_config_system)

# Register with CTest
gtest_discover_tests(test_page_size_config_system
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "system;hardware;vfio;page_size;config"
)

# ============================================================================
# Module 54: CUDA Host Memory System Tests
# ============================================================================

add_executable(test_cuda_host_io_system
    54_test_cuda_host_io_system.cpp
)

target_include_directories(test_cuda_host_io_system PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_cuda_host_io_system PRIVATE
    device_detector
    device_detector
    setup_helper
    system_test_config
    mapping_host
    host_io_host_mem
    cuda_io_host_mem          # Module 54: CUDA host memory library
    nvme_patterns             # For data pattern verification
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

# Add profiling targets
add_profiling_targets(test_cuda_host_io_system)

# Register with CTest
gtest_discover_tests(test_cuda_host_io_system
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "system;hardware;vfio;cuda;module54"
)

message(STATUS "Module 53 System Tests:")
message(STATUS "  - test_host_io_system: Combined MMIO + SetupHelper host I/O flows")
message(STATUS "  - test_page_size_config_system: Page size configuration and validation")
message(STATUS "")
message(STATUS "Module 54 System Tests:")
message(STATUS "  - test_cuda_host_io_system: CUDA host-pinned memory integration with NVMe")
message(STATUS "")
message(STATUS "=== Sudo Setup Required ===")
message(STATUS "Tests require root privileges for VFIO operations.")
message(STATUS "To configure passwordless sudo (recommended):")
message(STATUS "  ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/scripts/sudo_setup/setup_sudo_nopasswd.sh")
message(STATUS "")
message(STATUS "To run system tests:")
message(STATUS "  1. Setup environment:")
message(STATUS "       export NVME_BDF=\"0000:41:00.0\"")
message(STATUS "       export NVME_NSID=\"1\"")
message(STATUS "       export NVME_LBA_SIZE=\"512\"")
message(STATUS "       export NVME_SLBA=\"2000000\"  # Safe test area")
message(STATUS "")
message(STATUS "  2. Bind NVMe device to vfio-pci (if sudo setup done):")
message(STATUS "       sudo /usr/local/sbin/vfio-bind.sh $NVME_BDF")
message(STATUS "")
message(STATUS "  3. Run tests:")
message(STATUS "       sudo -E ./test_host_io_system")
message(STATUS "")
message(STATUS "  4. Restore device (when done):")
message(STATUS "       sudo /usr/local/sbin/vfio-unbind.sh $NVME_BDF")
message(STATUS "")

# ============================================================================
# Module 55.1: Host Daemon Doorbell System Tests
# ============================================================================

add_executable(test_host_daemon_doorbell
    55.1_test_host_daemon_doorbell.cpp
)

target_include_directories(test_host_daemon_doorbell PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_host_daemon_doorbell PRIVATE
    setup_helper
    system_test_config
    device_detector
    mapping_host
    host_io_host_mem
    nvme_patterns        # For data pattern verification
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

add_profiling_targets(test_host_daemon_doorbell)

gtest_discover_tests(test_host_daemon_doorbell
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "system;hardware;vfio;host_daemon;module55_1"
)

# ============================================================================
# Module 55.2: Shadow Doorbell Buffer Tests
# ============================================================================

add_executable(test_shadow_doorbell
    55.2_test_shadow_doorbell.cpp
)

target_include_directories(test_shadow_doorbell PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_shadow_doorbell PRIVATE
    setup_helper
    system_test_config
    device_detector
    mapping_host
    host_io_host_mem
    nvme_patterns        # For data pattern verification
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

add_profiling_targets(test_shadow_doorbell)

gtest_discover_tests(test_shadow_doorbell
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF}"
        LABELS "system;hardware;vfio;dbc;module55_2"
)

# ============================================================================
# Module 55.3: Host DBC Daemon Tests
# ============================================================================

add_executable(test_host_dbc_daemon
    55.3_test_host_dbc_daemon.cpp
)

target_include_directories(test_host_dbc_daemon PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_host_dbc_daemon PRIVATE
    setup_helper
    system_test_config
    device_detector
    mapping_host
    host_io_host_mem
    nvme_patterns        # For data pattern verification
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

add_profiling_targets(test_host_dbc_daemon)

gtest_discover_tests(test_host_dbc_daemon
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF}"
        LABELS "system;hardware;vfio;dbc_daemon;module55_3"
)

# ============================================================================
# Module 55.4: Mode Comparison Harness
# ============================================================================

add_executable(test_mode_comparison_harness
    55.4_test_mode_comparison_harness.cpp
)

target_include_directories(test_mode_comparison_harness PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_mode_comparison_harness PRIVATE
    setup_helper
    system_test_config
    device_detector
    mapping_host
    host_io_host_mem
    nvme_patterns        # For data pattern verification
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

add_profiling_targets(test_mode_comparison_harness)

gtest_discover_tests(test_mode_comparison_harness
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF}"
        LABELS "system;hardware;vfio;mode_comparison;module55_4"
)

# ============================================================================
# Module 56: GPU Queue + GPU Buffer Tests
# ============================================================================

add_executable(test_gpu_queue_gpu_buffer
    56_test_gpu_queue_gpu_buffer.cpp
)

set_source_files_properties(56_test_gpu_queue_gpu_buffer.cpp PROPERTIES LANGUAGE CUDA)

target_include_directories(test_gpu_queue_gpu_buffer PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_gpu_queue_gpu_buffer PRIVATE
    setup_helper
    system_test_config
    device_detector
    mapping_host
    host_io_host_mem
    nvme_patterns        # For data pattern verification
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

add_profiling_targets(test_gpu_queue_gpu_buffer)

gtest_discover_tests(test_gpu_queue_gpu_buffer
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF}"
        LABELS "system;hardware;vfio;gpu_queue;module56"
)

add_executable(test_gpu_cq_gpu_buffer
    test_gpu_cq_gpu_buffer.cpp
)

set_source_files_properties(test_gpu_cq_gpu_buffer.cpp PROPERTIES LANGUAGE CUDA)

target_include_directories(test_gpu_cq_gpu_buffer PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

target_link_libraries(test_gpu_cq_gpu_buffer PRIVATE
    mapping_host
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gtest_main
)

add_profiling_targets(test_gpu_cq_gpu_buffer)

gtest_discover_tests(test_gpu_cq_gpu_buffer
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF}"
        LABELS "system;hardware;vfio;gpu_queue;gpu_cq;module56"
)
