# Test executables for Training Infrastructure
add_executable(${MODULE}_test
    # Tests for host-side training orchestration
    unit/host/test_training_loop.cpp

    # Tests for GPU kernels
    unit/kernels/test_adamw.cu
    unit/kernels/test_loss.cu
    unit/kernels/test_gradients.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib      # Gets src/ (INTERFACE) for including kernel sources
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB} # Gets 00.test_lib path automatically
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
