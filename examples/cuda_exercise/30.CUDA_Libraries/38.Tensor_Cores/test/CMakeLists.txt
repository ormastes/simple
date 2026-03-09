add_executable(${MODULE}_test
    unit/test_wmma.cu
)

target_link_libraries(${MODULE}_test PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB}
)

target_compile_options(${MODULE}_test PRIVATE
    $<$<COMPILE_LANGUAGE:CUDA>:-arch=sm_75>
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
