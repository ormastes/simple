# Test executables for GPT Architecture
add_executable(${MODULE}_test
    unit/kernels/test_gpt_model.cu
    unit/kernels/test_sampling.cu
    unit/kernels/test_text_generator.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
