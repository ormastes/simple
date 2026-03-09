# Test executables for GPUDirect Storage

# Unit tests (all compiled as CUDA since they use gpu_gtest.h)
add_executable(${MODULE}_test
    # cuFile wrapper tests
    unit/common/test_cufile_wrapper.cu
    # Pattern kernel tests
    unit/kernels/test_pattern_kernels.cu
    # Integration tests
    integration/test_gds_read_write.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
)

# Discover tests
gtest_discover_tests(${MODULE}_test)

# Add profiling targets
add_profiling_targets(${MODULE}_test)
