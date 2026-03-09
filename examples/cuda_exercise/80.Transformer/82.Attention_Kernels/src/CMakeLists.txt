add_library(${MODULE}_lib STATIC
    kernels/flash_attention.cu
    kernels/rope.cu
    kernels/kv_cache.cu
    kernels/softmax.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib ${CUDA_BASIC_LIB}
    87_Attention_Common_API_lib
    86_Core_Common_API_lib
)

add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
