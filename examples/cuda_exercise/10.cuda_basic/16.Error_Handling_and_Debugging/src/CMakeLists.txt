add_library(${MODULE}_lib_INTERFACE
INTERFACE
)
target_include_directories(${MODULE}_lib_INTERFACE
INTERFACE
    ${CMAKE_CURRENT_LIST_DIR}
)

add_library(${MODULE}_lib
STATIC
    kernels/vector_add_2d.cu
)

target_link_libraries(${MODULE}_lib
    PUBLIC
    ${CUDA_BASIC_LIB}
    ${MODULE}_lib_INTERFACE
)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
