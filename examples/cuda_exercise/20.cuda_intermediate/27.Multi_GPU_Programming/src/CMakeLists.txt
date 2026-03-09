# Source library for Multi-GPU Programming (Module 27)
# Extends Module 26 cooperative groups to multi-GPU execution

add_library(${MODULE}_lib STATIC
    # Multi-GPU kernels (enhanced from Module 26)
    kernels/matrix_multiply_multi_gpu.cu
    kernels/vector_ops_multi_gpu.cu
    # Host-side multi-GPU management
    host/multi_gpu_manager.cpp
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}  # Allows tests to include kernels/*.cu
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/host  # For multi_gpu_manager.h
)

# Link dependencies (automatically propagates their include paths)
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib  # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
)

# Set CUDA properties for multi-GPU and cooperative groups
# Requires compute capability 6.0+ for cooperative groups
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
