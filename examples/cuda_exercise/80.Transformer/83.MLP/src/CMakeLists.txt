add_library(${MODULE}_lib STATIC
    kernels/activation.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib ${CUDA_BASIC_LIB}
    81_Core_GEMM_Operations_lib
)
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in)
