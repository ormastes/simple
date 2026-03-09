# Test executables
add_executable(${MODULE}_test
    unit/kernels/test_dynamic_kernels.cu
    unit/kernels/test_matrix_multiply_dynamic.cu
    unit/kernels/test_vector_ops_dynamic.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
    cudadevrt
)

# Enable relocatable device code
set_target_properties(${MODULE}_test PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
)

gtest_discover_tests(${MODULE}_test)
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_test)
endif()
