add_library(${MODULE}_lib STATIC
    common/vector_io.cu
    common/layout_swizzle.cu
)
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
