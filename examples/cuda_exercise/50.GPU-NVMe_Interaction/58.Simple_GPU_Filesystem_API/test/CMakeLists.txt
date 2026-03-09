# -----------------------------------------------------------------------------
# Unit tests (mock NVMe device)
# -----------------------------------------------------------------------------
add_executable(${MODULE}_test
    unit/host/test_filesystem_basic.cpp
    unit/host/test_c_api.cpp
    unit/host/mock_nvme_impl.cpp
)

# Link to libraries
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    GTest::gtest
    GTest::gtest_main
    GTest::gmock
)

gtest_discover_tests(${MODULE}_test
    PROPERTIES
        LABELS "unit;filesystem;module58"
)
add_profiling_targets(${MODULE}_test)

# -----------------------------------------------------------------------------
# Integration tests (mock NVMe device, higher-level workflows)
# -----------------------------------------------------------------------------
add_executable(${MODULE}_integration_test
    integration/test_filesystem_integration.cpp
    unit/host/mock_nvme_impl.cpp  # Reuse mock implementation
)

target_include_directories(${MODULE}_integration_test PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/unit/host
)

target_link_libraries(${MODULE}_integration_test PRIVATE
    ${MODULE}_lib
    GTest::gtest
    GTest::gtest_main
    GTest::gmock
)

gtest_discover_tests(${MODULE}_integration_test
    PROPERTIES
        LABELS "integration;filesystem;module58"
)
add_profiling_targets(${MODULE}_integration_test)

# -----------------------------------------------------------------------------
# System tests (real NVMe hardware via Module 53)
# -----------------------------------------------------------------------------
# NOTE: system_test/ directory removed during Module 53 consolidation
# System testing functionality is now available via Module 53's test suite
# if(TARGET setup_helper AND TARGET device_detector)
#     add_subdirectory(system_test)
# else()
#     message(STATUS "Skipping Module 58 system tests (Module 53 infrastructure not available)")
# endif()
