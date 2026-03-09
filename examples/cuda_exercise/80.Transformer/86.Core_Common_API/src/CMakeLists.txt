add_library(${MODULE}_lib STATIC
    kernels/gemm_simt.cu
    kernels/gemm_wmma_tc.cu
    kernels/gemm_int8_dp4a.cu
    kernels/autotune_registry.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib ${CUDA_BASIC_LIB}
    89_Tensor_Ops_Common_API_lib
)

add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
