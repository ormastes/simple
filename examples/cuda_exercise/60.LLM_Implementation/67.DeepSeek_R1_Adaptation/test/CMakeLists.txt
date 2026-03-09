# Test executables for DeepSeek R1 Adaptation
add_executable(${MODULE}_test
    unit/kernels/test_gqa_attention.cu
    unit/kernels/test_rope_fused.cu
    unit/kernels/test_swiglu_fused.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
