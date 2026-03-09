# Source library for cuBLAS demonstrations
add_library(${MODULE}_lib STATIC
    matrix_multiply_demo.cu
    vector_operations.cu
    matrix_vector_ops.cu
    batched_operations.cu
)

# Export src/ as INTERFACE so tests can include source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}
)

# Link dependencies
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    CUDA::cublas
)

# Demo executable
add_executable(${MODULE}_demo demo_main.cu)
target_link_libraries(${MODULE}_demo PRIVATE ${MODULE}_lib)
add_profiling_targets(${MODULE}_demo)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
