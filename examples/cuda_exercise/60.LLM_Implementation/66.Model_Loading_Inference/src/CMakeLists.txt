add_library(${MODULE}_lib STATIC
    host/checkpoint.cpp
    host/huggingface_loader.cpp
    host/beam_search.cpp
    kernels/kv_cache_kernels.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB} 64_GPT_Architecture_lib)
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in)
