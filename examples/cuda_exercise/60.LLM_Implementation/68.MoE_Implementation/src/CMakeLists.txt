add_library(${MODULE}_lib STATIC
    kernels/router_kernels.cu
    kernels/expert_dispatch.cu
    kernels/expert_combine.cu
    kernels/load_balance_loss.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB} 67_DeepSeek_R1_Adaptation_lib)
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in)
