# Test executables for CUDA_IPC
set(TEST_SOURCES
    unit/test_ipc_basic.cu
)

add_executable(${MODULE}_test ${TEST_SOURCES})

target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB}
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
