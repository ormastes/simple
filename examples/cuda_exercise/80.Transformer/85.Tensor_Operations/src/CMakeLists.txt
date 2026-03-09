add_library(${MODULE}_lib STATIC
    kernels/bias_residual.cu
    kernels/transpose_permute.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib ${CUDA_BASIC_LIB}
    89_Tensor_Ops_Common_API_lib
)
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in)
