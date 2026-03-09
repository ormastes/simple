# Test executable
add_executable(${MODULE}_test
    # Tests for reusable stream-optimized kernels
    unit/kernels/test_streams_kernels.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib      # Gets src/ (INTERFACE) for including kernel sources
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB} # Gets 00.test_lib path automatically
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
