# -----------------------------------------------------------------------------
# Unit tests (C++/CUDA-free validation of configuration helpers)
# -----------------------------------------------------------------------------

add_executable(${MODULE}_unit_common
    unit/common/test_attention_types.cpp
    unit/common/test_expert_config.cpp
)

target_link_libraries(${MODULE}_unit_common PRIVATE
    attention_expert_kernels_59
    ${GTEST_BASIC_LIB}
)

gtest_discover_tests(${MODULE}_unit_common
    PROPERTIES
        LABELS "unit;attention;module59"
)
add_profiling_targets(${MODULE}_unit_common)

# -----------------------------------------------------------------------------
# Integration tests (PyTorch + Python)
# -----------------------------------------------------------------------------

if(NOT ATTENTION_EXPERT_TORCH_FOUND)
    message(STATUS "Skipping Module 59 integration tests (PyTorch bindings not built)")
    return()
endif()

find_package(Python3 COMPONENTS Interpreter QUIET)
if(NOT Python3_Interpreter_FOUND)
    message(WARNING "Python interpreter not found - skipping Module 59 integration and system tests")
    return()
endif()

set(TEST_ENV_PYTHONPATH "${CMAKE_CURRENT_SOURCE_DIR}/../python")

add_test(NAME 59_Attention_PyTorchIntegration
         COMMAND Python3::Interpreter
         ${CMAKE_CURRENT_SOURCE_DIR}/integration/test_pytorch_integration.py)
set_tests_properties(59_Attention_PyTorchIntegration PROPERTIES
    ENVIRONMENT "PYTHONPATH=${TEST_ENV_PYTHONPATH}:$ENV{PYTHONPATH}"
    DISABLED TRUE
    LABELS "integration;module59;attention")

add_test(NAME 59_Attention_NvmeLoading
         COMMAND Python3::Interpreter
         ${CMAKE_CURRENT_SOURCE_DIR}/integration/test_nvme_loading.py)
set_tests_properties(59_Attention_NvmeLoading PROPERTIES
    ENVIRONMENT "PYTHONPATH=${TEST_ENV_PYTHONPATH}:$ENV{PYTHONPATH}"
    DISABLED TRUE
    LABELS "integration;module59;attention")

# -----------------------------------------------------------------------------
# System tests (PyTorch + GPU + optional NVMe)
# -----------------------------------------------------------------------------

add_test(NAME 59_Attention_System
         COMMAND Python3::Interpreter
         ${CMAKE_CURRENT_SOURCE_DIR}/system_test/test_attention_system.py)
set_tests_properties(59_Attention_System PROPERTIES
    ENVIRONMENT "PYTHONPATH=${TEST_ENV_PYTHONPATH}:$ENV{PYTHONPATH};NVME_BDF=${NVME_BDF};NVME_NSID=${NVME_NSID};NVME_LBA_SIZE=${NVME_LBA_SIZE};NVME_SLBA=${NVME_SLBA}"
    DISABLED FALSE
    LABELS "system;module59;attention;gpu")

message(STATUS "Module 59 Tests:")
message(STATUS "  - Unit tests: test_attention_types, test_expert_config")
message(STATUS "  - Integration tests: PyTorch integration, NVMe loading")
message(STATUS "  - System tests: Complete attention expert pipeline")
message(STATUS "")
message(STATUS "To run system tests:")
message(STATUS "  cd build && ctest -R 59_Attention_System -V")
message(STATUS "  Or: cd test/system_test && python3 test_attention_system.py")
