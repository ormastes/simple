# Module 53 Test Helper Library

# ============================================================================
# Note: General-purpose utilities have been migrated to src/common/
#   - nvme_io_utils:   File LBA mapping (from nvme_test_file_utils) ✅
#   - nvme_patterns:   Data pattern generation (from pattern_helper) ✅
#
# Test-specific infrastructure remains in test/helper/:
#   - nvme_config:     Environment variable parsing for tests
#   - vfio_safety:     Device safety checks for test setup
#   - system_test_config: Test configuration utilities
#   - setup_helper:    Task-based test setup system
# ============================================================================

# VFIO Safety library (test infrastructure)
add_library(vfio_safety STATIC
    vfio_safety.cpp
)
target_include_directories(vfio_safety PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
)
target_link_libraries(vfio_safety PUBLIC ${CUDA_BASIC_LIB})
set_target_properties(vfio_safety PROPERTIES
    LINKER_LANGUAGE CXX
    CUDA_RESOLVE_DEVICE_SYMBOLS OFF
    CUDA_SEPARABLE_COMPILATION OFF
)

# System Test Config library (test configuration utilities)
add_library(system_test_config STATIC
    system_test_config.cpp
)
target_include_directories(system_test_config PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/..  # test/ directory (for helper/ includes)
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/src/common  # For device/ includes
)
target_link_libraries(system_test_config PUBLIC
    device_detector
)
set_target_properties(system_test_config PROPERTIES
    LINKER_LANGUAGE CXX
)

# device_chooser functionality has been merged into SystemFeatures/device_detector

# Setup Helper Library
add_library(setup_helper STATIC
    setup_helper.cpp
)

# Enable CUDA compilation for setup_helper.cpp (contains CUDA tasks)
set_source_files_properties(setup_helper.cpp PROPERTIES LANGUAGE CUDA)

target_include_directories(setup_helper PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/src
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/src/cuda_host
    ${CMAKE_SOURCE_DIR}/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/src/cuda_gpu
)

target_link_libraries(setup_helper PUBLIC
    mapping_host
    host_io_host_mem
    cuda_io_host_mem      # CUDA host (pinned) memory
    doorbell_daemon       # Doorbell daemon library
    dbc_setup            # DBC (shadow doorbell) setup library
    cuda_io_gpu_mem_55    # CUDA GPU (device) memory - Fixed!
    mapping_gpu_55        # GPU mapper for nvme_setup_gpu_queue()
    vfio_safety          # VFIO safety checks (for vfio_utils.h)
    ${CUDA_BASIC_LIB}
)

set_target_properties(setup_helper PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON
)

# Setup Helper Example (optional demo)
add_executable(setup_helper_example
    setup_helper_example.cpp
)

target_link_libraries(setup_helper_example PRIVATE
    setup_helper
    mapping_host
    host_io_host_mem
    ${CUDA_BASIC_LIB}
)

# Add profiling targets
add_profiling_targets(setup_helper_example)

# Shadow DB controller runner (used by tests when RUN_SHADOW_DB_CONTROLLER=1)
add_executable(shadow_db_controller_runner
    tools/shadow_db_controller_runner.cpp
)
target_link_libraries(shadow_db_controller_runner PRIVATE
    setup_helper
    mapping_host
    host_io_host_mem
    doorbell_daemon
    ${CUDA_BASIC_LIB}
)
add_profiling_targets(shadow_db_controller_runner)

message(STATUS "Module 53 Test Helpers:")
message(STATUS "  - nvme_test_helper: NVMe test file utilities library")
message(STATUS "  - device selection: Integrated into SystemFeatures/device_detector")
message(STATUS "  - setup_helper: Task-based test setup system")
message(STATUS "  - setup_helper_example: Demo of SetupHelper usage")
message(STATUS "  - shadow_db_controller_runner: Host-side shadow DB -> MMIO mirror (optional)")
