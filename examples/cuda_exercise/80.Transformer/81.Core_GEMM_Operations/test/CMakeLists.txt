add_executable(${MODULE}_test
    unit/kernels/test_gemm_ops.cu
)
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB}
)
gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
