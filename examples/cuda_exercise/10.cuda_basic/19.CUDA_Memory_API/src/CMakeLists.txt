# Interface library for headers
add_library(${MODULE}_lib_INTERFACE INTERFACE)
target_include_directories(${MODULE}_lib_INTERFACE
    INTERFACE
    ${CMAKE_CURRENT_LIST_DIR}
)

# Source library for Part 19 - CUDA Memory API (enhanced kernels from previous parts)
add_library(${MODULE}_lib STATIC
    kernels/matrix_multiply.cu
    kernels/vector_add_2d.cu
)

target_compile_definitions(${MODULE}_lib PUBLIC BUILDING_LIB)

target_link_libraries(${MODULE}_lib
    PUBLIC
    ${MODULE}_lib_INTERFACE
    ${CUDA_BASIC_LIB}
)

# Part-specific library for memory API demonstrations
add_library(${MODULE}_memory_lib STATIC
    part_specific/memory_api_demo.cu
)

target_link_libraries(${MODULE}_memory_lib
    PUBLIC
    ${MODULE}_lib_INTERFACE
    ${CUDA_BASIC_LIB}
)

# Note: Main executable removed - Part 19+ uses tests instead of main()

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
