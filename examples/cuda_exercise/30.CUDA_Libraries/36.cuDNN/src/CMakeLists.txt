add_executable(${MODULE}_cudnn_basics cudnn_basics.cu)
target_link_libraries(${MODULE}_cudnn_basics PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} CUDA::cudnn
)
add_profiling_targets(${MODULE}_cudnn_basics)

add_executable(${MODULE}_cudnn_conv cudnn_conv.cu)
target_link_libraries(${MODULE}_cudnn_conv PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} CUDA::cudnn
)
add_profiling_targets(${MODULE}_cudnn_conv)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
