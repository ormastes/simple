add_executable(${MODULE}_test
    unit/kernels/test_flash_attention.cu
    unit/kernels/test_rope.cu
    unit/kernels/test_kv_cache.cu
    unit/kernels/test_softmax.cu
)
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB}
)
gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
