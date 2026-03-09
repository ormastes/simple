add_library(${MODULE}_lib STATIC
    host/c_api.cpp
    kernels/similarity_kernels.cu
    kernels/quantize_kernels.cu
    kernels/pipeline_kernels.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib ${CUDA_BASIC_LIB}
    68_MoE_Implementation_lib
    66_Model_Loading_Inference_lib
)
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in)
