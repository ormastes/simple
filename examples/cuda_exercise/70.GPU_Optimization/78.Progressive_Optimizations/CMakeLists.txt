project(78_Progressive_Optimizations CUDA CXX)
set(MODULE ${PROJECT_NAME})

find_package(CUDAToolkit REQUIRED)

# Matmul optimization stages
add_library(${MODULE}_matmul_lib STATIC
    src/matmul/01_naive.cu
    src/matmul/02_shared_memory.cu
    src/matmul/03_tiled.cu
    src/matmul/04_vectorized.cu
    src/matmul/05_wmma.cu
)
target_include_directories(${MODULE}_matmul_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src)
target_link_libraries(${MODULE}_matmul_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

# Backprop optimization stages
add_library(${MODULE}_backprop_lib STATIC
    src/backprop/01_naive.cu
    src/backprop/02_fused.cu
    src/backprop/03_optimized.cu
)
target_include_directories(${MODULE}_backprop_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src)
target_link_libraries(${MODULE}_backprop_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

# Attention optimization stages
add_library(${MODULE}_attention_lib STATIC
    src/attention/01_naive.cu
    src/attention/02_tiled.cu
    src/attention/03_flash_v2.cu
)
target_include_directories(${MODULE}_attention_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src)
target_link_libraries(${MODULE}_attention_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

# Combined library
add_library(${MODULE}_lib INTERFACE)
target_link_libraries(${MODULE}_lib INTERFACE
    ${MODULE}_matmul_lib ${MODULE}_backprop_lib ${MODULE}_attention_lib
)

# Tests
if(BUILD_TESTING)
    add_executable(${MODULE}_test
        test/unit/test_matmul_stages.cu
        test/unit/test_backprop_stages.cu
        test/unit/test_attention_stages.cu
    )
    target_link_libraries(${MODULE}_test PRIVATE
        ${MODULE}_matmul_lib ${MODULE}_backprop_lib ${MODULE}_attention_lib
        ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB}
    )
    gtest_discover_tests(${MODULE}_test)
    add_profiling_targets(${MODULE}_test)
endif()
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in)
