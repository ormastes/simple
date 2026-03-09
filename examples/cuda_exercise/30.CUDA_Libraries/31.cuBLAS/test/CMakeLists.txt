# Test executable for cuBLAS
add_executable(${MODULE}_test
    unit/test_cublas_basic.cu
    unit/test_matrix_multiply.cu
    unit/test_batched_operations.cu
)

# Link to libraries
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${GTEST_BASIC_LIB}
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
