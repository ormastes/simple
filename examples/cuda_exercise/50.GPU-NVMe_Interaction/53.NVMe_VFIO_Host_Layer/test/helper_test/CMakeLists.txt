add_executable(device_selector_tests
    device_chooser_test.cpp
)

target_link_libraries(device_selector_tests PRIVATE
    device_detector
    ${CUDA_BASIC_LIB}
    GTest::gtest_main
    GTest::gtest
    GTest::gmock
)

target_include_directories(device_selector_tests PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

add_profiling_targets(device_selector_tests)

gtest_discover_tests(device_selector_tests
    PROPERTIES
        LABELS "helper;device"
)

# Setup Helper Hardware Tests
add_executable(test_setup_tasks
    test_setup_tasks.cpp
)

# Enable CUDA compilation for test_setup_tasks.cpp (contains CUDA tests)
set_source_files_properties(test_setup_tasks.cpp PROPERTIES LANGUAGE CUDA)

target_include_directories(test_setup_tasks PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..  # For helper/setup_helper.h
)

target_link_libraries(test_setup_tasks PRIVATE
    setup_helper
    device_detector
    mapping_host
    host_io_host_mem
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

set_target_properties(test_setup_tasks PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON
)

# Add profiling targets
add_profiling_targets(test_setup_tasks)

# Register with CTest
gtest_discover_tests(test_setup_tasks
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "helper_test;hardware;vfio;setup_tasks"
)

# SetupHelper Host I/O Integration Tests
add_executable(test_setup_helper_host_io
    test_setup_helper_host_io.cpp
)

target_include_directories(test_setup_helper_host_io PRIVATE
    ${CMAKE_SOURCE_DIR}/00.test_lib
    ${CMAKE_CURRENT_SOURCE_DIR}/..  # For helper/setup_helper.h
)

target_link_libraries(test_setup_helper_host_io PRIVATE
    setup_helper
    device_detector
    mapping_host
    host_io_host_mem
    nvme_patterns        # Migrated from pattern_helper
    ${CUDA_BASIC_LIB}
    GTest::gtest
    GTest::gmock
)

# Add profiling targets
add_profiling_targets(test_setup_helper_host_io)

# Register with CTest
gtest_discover_tests(test_setup_helper_host_io
    PROPERTIES
        ENVIRONMENT "NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
        LABELS "helper_test;hardware;vfio;setup_helper_host_io"
)
