# Test executables for cuFFT module

add_executable(${MODULE}_test
    unit/test_cufft_1d.cu
    unit/test_cufft_2d.cu
)

target_link_libraries(${MODULE}_test PRIVATE
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
    CUDA::cufft
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
