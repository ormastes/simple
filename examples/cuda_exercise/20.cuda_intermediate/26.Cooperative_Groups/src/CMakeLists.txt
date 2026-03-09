# Source library for Cooperative Groups (Module 26)
# Mirrors Module 25 structure but uses cooperative groups instead of dynamic parallelism
add_library(${MODULE}_lib STATIC
    # Cooperative groups kernels (same patterns as Module 25)
    kernels/matrix_multiply_cg.cu
    kernels/vector_ops_cg.cu
    part_specific/cg_kernels.cu
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}  # Allows tests to include kernels/*.cu
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/kernels  # For cg_kernels.h
)

# Link dependencies
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib  # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
)

# Set CUDA properties for cooperative groups
# Cooperative groups require compute capability 6.0+ but will use default architecture
set_target_properties(${MODULE}_lib PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
