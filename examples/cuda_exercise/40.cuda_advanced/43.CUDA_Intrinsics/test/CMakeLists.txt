# Test executables for CUDA_Intrinsics
set(TEST_SOURCES
    unit/test_warp_shuffle.cu
    unit/test_warp_vote.cu
    unit/test_math_intrinsics.cu
)

add_executable(${MODULE}_test ${TEST_SOURCES})

target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
