# Test executables
add_executable(${MODULE}_test
    # Tests for reusable shared memory kernels (from module 22)
    unit/kernels/test_shared_memory_kernels.cu
    # NEW: Tests for cooperative groups kernels (enhanced from Module 25)
    unit/kernels/test_cooperative_groups.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib      # Gets src/ (INTERFACE) for including kernel sources
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB} # Gets 00.test_lib path automatically
)

gtest_discover_tests(${MODULE}_test)
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_test)
endif()
