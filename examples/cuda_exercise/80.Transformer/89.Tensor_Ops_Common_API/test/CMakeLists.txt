add_executable(${MODULE}_test
    unit/kernels/test_vector_io.cu
    unit/kernels/test_layout_swizzle.cu
)

target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
