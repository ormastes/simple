# Unit Tests for Module 53: NVMe VFIO Host Layer

# ============================================================================
# Helper macro to configure test executables (pure C++, no CUDA)
# ============================================================================

macro(configure_cpp_test_target target_name)
    # Add test directory to include path for test helpers
    target_include_directories(${target_name} PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/..  # test/ directory
        ${CMAKE_CURRENT_SOURCE_DIR}/../helper  # test/helper/ for nvme_test_helper.h
    )

    set_target_properties(${target_name} PROPERTIES
        LINKER_LANGUAGE CXX
        CUDA_RESOLVE_DEVICE_SYMBOLS OFF
        CUDA_SEPARABLE_COMPILATION OFF
    )
    gtest_discover_tests(${target_name})
    add_profiling_targets(${target_name})
endmacro()

# ============================================================================
# Unit Tests - Common (Utilities and Helpers)
# ============================================================================

add_executable(test_utility_functions_53 common/test_utility_functions.cpp)
target_link_libraries(test_utility_functions_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_utility_functions_53)

add_executable(test_memory_buffer_utils_53 common/test_memory_buffer_utils.cpp)
target_link_libraries(test_memory_buffer_utils_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_memory_buffer_utils_53)

add_executable(test_doorbell_strategies_53 common/test_doorbell_strategies.cpp)
target_link_libraries(test_doorbell_strategies_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_doorbell_strategies_53)

add_executable(test_buffer_factory_53 common/test_buffer_factory.cpp)
target_link_libraries(test_buffer_factory_53 PRIVATE nvme_vio_host buffer_factory ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_buffer_factory_53)

add_executable(test_buffer_factory_c_interface_53 common/test_buffer_factory_c_interface.cpp)
target_link_libraries(test_buffer_factory_c_interface_53 PRIVATE nvme_vio_host buffer_factory ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_buffer_factory_c_interface_53)

# ============================================================================
# Unit Tests - Host (Host-side I/O Implementation)
# ============================================================================

add_executable(test_host_io_host_mem_53 host/test_host_io_host_mem.cpp)
target_link_libraries(test_host_io_host_mem_53 PRIVATE host_io_host_mem nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_host_io_host_mem_53)

add_executable(test_prp_edge_cases_53 host/test_prp_edge_cases.cpp)
target_link_libraries(test_prp_edge_cases_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_prp_edge_cases_53)

add_executable(test_template_combinations_53 host/test_template_combinations.cpp)
target_link_libraries(test_template_combinations_53 PRIVATE host_io_host_mem nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_template_combinations_53)

# ============================================================================
# Unit Tests - Part Specific (NVMe VFIO Specific)
# ============================================================================

add_executable(test_nvme_vio_host_53 part_specific/test_nvme_vio_host.cpp)
target_link_libraries(test_nvme_vio_host_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_nvme_vio_host_53)

add_executable(test_nvme_page_size_53 part_specific/test_nvme_page_size.cpp)
target_link_libraries(test_nvme_page_size_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_nvme_page_size_53)

add_executable(test_doorbell_support_53 part_specific/test_doorbell_support.cpp)
target_link_libraries(test_doorbell_support_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_doorbell_support_53)

add_executable(test_nvme_vio_host_buffer_53 part_specific/test_nvme_vio_host_buffer.cpp)
target_link_libraries(test_nvme_vio_host_buffer_53 PRIVATE nvme_vio_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_nvme_vio_host_buffer_53)

# ============================================================================
# Unit Tests - Queue (Queue Factory and Management)
# ============================================================================

add_executable(test_factory_methods_53 queue/test_factory_methods.cpp)
target_link_libraries(test_factory_methods_53 PRIVATE nvme_vio_host mapping_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_factory_methods_53)

# ============================================================================
# Unit Tests - CUDA Host (Module 54 - CUDA Host Memory)
# ============================================================================

add_executable(test_cuda_io_host_mem_53 cuda_host/test_cuda_io_host_mem.cpp)
target_link_libraries(test_cuda_io_host_mem_53 PRIVATE cuda_io_host_mem nvme_vio_cuda_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_cuda_io_host_mem_53)

add_executable(test_nvme_vio_cuda_host_buffer_53 cuda_host/test_nvme_vio_cuda_host_buffer.cpp)
target_link_libraries(test_nvme_vio_cuda_host_buffer_53 PRIVATE nvme_vio_cuda_host ${GTEST_BASIC_LIB})
configure_cpp_test_target(test_nvme_vio_cuda_host_buffer_53)

message(STATUS "Module 53 Unit Tests:")
message(STATUS "  Common: test_utility_functions_53, test_memory_buffer_utils_53, test_doorbell_strategies_53")
message(STATUS "  Buffer Factory: test_buffer_factory_53, test_buffer_factory_c_interface_53")
message(STATUS "  Host: test_host_io_host_mem_53, test_prp_edge_cases_53, test_template_combinations_53")
message(STATUS "  Part Specific: test_nvme_vio_host_53, test_nvme_page_size_53, test_doorbell_support_53, test_nvme_vio_host_buffer_53")
message(STATUS "  Queue: test_factory_methods_53")
message(STATUS "  CUDA Host: test_cuda_io_host_mem_53, test_nvme_vio_cuda_host_buffer_53")
