# Tensor Cores demo executables

add_executable(${MODULE}_wmma_basic wmma_basic.cu)
target_link_libraries(${MODULE}_wmma_basic PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB}
)
target_compile_options(${MODULE}_wmma_basic PRIVATE
    $<$<COMPILE_LANGUAGE:CUDA>:-arch=sm_75>  # Minimum for Tensor Cores
)
add_profiling_targets(${MODULE}_wmma_basic)

add_executable(${MODULE}_wmma_matmul wmma_matmul.cu)
target_link_libraries(${MODULE}_wmma_matmul PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB}
)
target_compile_options(${MODULE}_wmma_matmul PRIVATE
    $<$<COMPILE_LANGUAGE:CUDA>:-arch=sm_75>
)
add_profiling_targets(${MODULE}_wmma_matmul)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
