project(77_PyTorch_Native_CUDA CUDA CXX)
set(MODULE ${PROJECT_NAME})

find_package(CUDAToolkit REQUIRED)

# Core CUDA kernels (always built)
add_library(${MODULE}_lib STATIC
    src/cuda/matmul_cuda.cu
    src/cuda/backprop_cuda.cu
    src/cuda/attention_cuda.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src/cuda)
target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

# Tests
if(BUILD_TESTING)
    add_executable(${MODULE}_test test/unit/test_native_ops.cu)
    target_link_libraries(${MODULE}_test PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB})
    gtest_discover_tests(${MODULE}_test)
endif()

add_profiling_targets(${MODULE}_lib)
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in)
