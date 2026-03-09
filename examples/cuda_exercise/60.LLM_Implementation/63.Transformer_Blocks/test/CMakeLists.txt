# Test executables
add_executable(${MODULE}_test
    # Tests for normalization layers
    unit/kernels/test_layer_norm.cu
    unit/kernels/test_rms_norm.cu

    # Tests for feed-forward network
    unit/kernels/test_feed_forward.cu

    # Tests for complete transformer block
    unit/kernels/test_transformer_block.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib      # Gets src/ (INTERFACE) for including kernel sources
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB} # Gets 00.test_lib path automatically
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
