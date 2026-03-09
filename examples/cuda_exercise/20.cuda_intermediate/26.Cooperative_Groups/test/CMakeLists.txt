# Test executables for Cooperative Groups (Module 26)
add_executable(${MODULE}_test
    # Basic tests for cooperative groups kernels
    unit/kernels/test_cg_basic.cu
    # TODO: Add comprehensive tests when function signatures are aligned
    # unit/kernels/test_cg_reduction.cu
    # unit/kernels/test_cg_patterns.cu
    # unit/kernels/test_cg_matrix.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib      # Gets src/ (INTERFACE) for including kernel sources
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB} # Gets 00.test_lib path automatically
)

# Ensure cooperative groups support
set_target_properties(${MODULE}_test PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
)

gtest_discover_tests(${MODULE}_test)

# Add profiling targets for performance analysis
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_test)
endif()
