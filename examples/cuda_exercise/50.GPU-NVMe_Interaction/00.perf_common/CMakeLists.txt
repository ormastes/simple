cmake_minimum_required(VERSION 3.18)
project(perf_common CUDA CXX)

# Performance test common library
add_library(perf_common STATIC
    src/perf_stats.cpp
    src/gpu_kernels.cu
)

# Set include directories
target_include_directories(perf_common PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/include
)

# Link CUDA runtime
target_link_libraries(perf_common PUBLIC
    ${CUDA_LIBRARIES}
    ${CUDA_RUNTIME_LIBRARIES}
)

# Set CUDA properties
set_target_properties(perf_common PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_ARCHITECTURES "${CMAKE_CUDA_ARCHITECTURES}"
    POSITION_INDEPENDENT_CODE ON
)

# Export for use by other modules
set(PERF_COMMON_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/include PARENT_SCOPE)
set(PERF_COMMON_LIB perf_common PARENT_SCOPE)