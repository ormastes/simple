# Reusable kernels library for dynamic parallelism
add_library(${MODULE}_lib STATIC
    # Reusable kernels from Module 24, enhanced with dynamic parallelism
    kernels/matrix_multiply_dynamic.cu
    kernels/vector_ops_dynamic.cu
    # Module-specific dynamic parallelism demonstrations
    part_specific/dynamic_kernels.cu
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}
)

# Link dependencies (must include cudadevrt for dynamic parallelism)
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    cudadevrt
)

# Enable relocatable device code and resolve device symbols
set_target_properties(${MODULE}_lib PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON
)

# Demo executables demonstrating dynamic parallelism

# Comprehensive demo
add_executable(${MODULE}_dynamic_demo part_specific/dynamic_demo.cu)
target_link_libraries(${MODULE}_dynamic_demo PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB} cudadevrt)
set_target_properties(${MODULE}_dynamic_demo PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON)
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_dynamic_demo)
endif()

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
