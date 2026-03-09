# Test executables for Attention Mechanisms
add_executable(${MODULE}_test
    # Tests for host-side setup
    unit/host/test_attention_setup.cu

    # Tests for attention kernels
    unit/kernels/test_attention_naive.cu
    unit/kernels/test_multi_head_attention.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib      # Gets src/ (INTERFACE) for including headers
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB} # Gets 00.test_lib path automatically
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
