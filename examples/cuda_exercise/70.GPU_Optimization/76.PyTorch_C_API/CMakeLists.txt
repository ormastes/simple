project(76_PyTorch_C_API CUDA CXX)
set(MODULE ${PROJECT_NAME})

find_package(CUDAToolkit REQUIRED)

# Core CUDA library (always built)
add_library(${MODULE}_lib STATIC
    src/kernels/matmul_kernel.cu
    src/c_api/torch_matmul_api.cpp
    src/c_api/torch_backprop_api.cpp
    src/c_api/torch_attention_api.cpp
)
target_include_directories(${MODULE}_lib PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/src/c_api
    ${CMAKE_CURRENT_SOURCE_DIR}/src/kernels
)
target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

# Shared library for Python ctypes
add_library(torch_cuda_ops SHARED
    src/kernels/matmul_kernel.cu
    src/c_api/torch_matmul_api.cpp
    src/c_api/torch_backprop_api.cpp
    src/c_api/torch_attention_api.cpp
)
target_include_directories(torch_cuda_ops PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/src/c_api
    ${CMAKE_CURRENT_SOURCE_DIR}/src/kernels
)
target_link_libraries(torch_cuda_ops PRIVATE CudaCustomLib ${CUDA_BASIC_LIB})
set_target_properties(torch_cuda_ops PROPERTIES PREFIX "" OUTPUT_NAME "libtorch_cuda_ops" SUFFIX ".so")

# Tests
if(BUILD_TESTING)
    add_executable(${MODULE}_test
        test/unit/test_torch_api.cu
        test/unit/test_matmul_kernel.cu
    )
    target_link_libraries(${MODULE}_test PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB})
    gtest_discover_tests(${MODULE}_test)
endif()

add_profiling_targets(${MODULE}_lib)
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in)
