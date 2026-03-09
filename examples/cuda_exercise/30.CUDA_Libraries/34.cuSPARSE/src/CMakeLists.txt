add_executable(${MODULE}_sparse_basics sparse_basics.cu)
target_link_libraries(${MODULE}_sparse_basics PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} CUDA::cusparse
)
add_profiling_targets(${MODULE}_sparse_basics)

add_executable(${MODULE}_sparse_matmul sparse_matmul.cu)
target_link_libraries(${MODULE}_sparse_matmul PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} CUDA::cusparse
)
add_profiling_targets(${MODULE}_sparse_matmul)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
