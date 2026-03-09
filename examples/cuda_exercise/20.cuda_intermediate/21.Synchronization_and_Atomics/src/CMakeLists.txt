# Source library for synchronization and atomics
# Includes both reusable kernels and part-specific implementations
add_library(${MODULE}_lib STATIC
    # Reusable kernels demonstrating synchronization patterns
    kernels/matrix_multiply_sync.cu
    kernels/vector_add_sync.cu
    # Part-specific demonstration code
    part_specific/atomic_operations.cu
    part_specific/synchronization_primitives.cu
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}  # Allows tests to include kernels/*.cu
)

target_compile_definitions(${MODULE}_lib PUBLIC BUILDING_LIB)

target_compile_options(${MODULE}_lib PRIVATE
    $<$<COMPILE_LANGUAGE:CUDA>:-rdc=true>
)

set_target_properties(${MODULE}_lib PROPERTIES
    CUDA_SEPARABLE_COMPILATION ON
    CUDA_RESOLVE_DEVICE_SYMBOLS ON
)

target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
