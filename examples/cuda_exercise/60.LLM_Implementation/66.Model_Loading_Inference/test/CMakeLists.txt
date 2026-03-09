add_executable(${MODULE}_test
    unit/host/test_checkpoint.cu
    unit/host/test_beam_search.cu
    unit/kernels/test_kv_cache.cu
)
target_link_libraries(${MODULE}_test PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB})
gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
