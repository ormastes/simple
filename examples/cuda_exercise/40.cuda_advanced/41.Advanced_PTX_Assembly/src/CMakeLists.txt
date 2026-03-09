# Source library for Advanced PTX Assembly
add_library(${MODULE}_lib INTERFACE)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}  # Allows tests to include kernels/*.cu
)

# Link dependencies (automatically propagates their include paths)
target_link_libraries(${MODULE}_lib INTERFACE
    CudaCustomLib  # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
)

# Demo executable demonstrating PTX features
add_executable(${MODULE}_demo part_specific/ptx_demo.cu)
target_link_libraries(${MODULE}_demo PRIVATE ${MODULE}_lib)
add_profiling_targets(${MODULE}_demo)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
