add_executable(${MODULE}_test
    unit/test_curand_host.cu
    unit/test_curand_device.cu
)

target_link_libraries(${MODULE}_test PRIVATE
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
    CUDA::curand
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
