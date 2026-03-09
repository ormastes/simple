add_executable(${MODULE}_test
    unit/test_sparse.cu
)

target_link_libraries(${MODULE}_test PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB} CUDA::cusparse
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
