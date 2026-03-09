# Test executables
add_executable(${MODULE}_test
    unit/kernels/test_coalescing_patterns.cu
    unit/kernels/test_bank_conflicts.cu
    unit/kernels/test_optimized_kernels.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}  # Gets 00.test_lib path automatically
)

gtest_discover_tests(${MODULE}_test)
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_test)
endif()
