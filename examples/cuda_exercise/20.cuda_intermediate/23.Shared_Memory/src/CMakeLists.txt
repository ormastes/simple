# Source library for Shared Memory demonstrations
add_library(${MODULE}_lib STATIC
    # Reusable shared memory kernels from module 22
    kernels/matrix_multiply_streams.cu
    kernels/vector_ops_streams.cu
    # NEW: Cooperative Groups kernels (enhanced from Module 25)
    kernels/cooperative_groups_reduction.cu
    kernels/cooperative_groups_patterns.cu
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}  # Allows tests to include kernels/*.cu
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/kernels  # For cooperative_groups_kernels.h
)

# Link dependencies
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib  # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
)

# Demo executables demonstrating shared memory patterns
add_executable(${MODULE}_transpose_demo part_specific/matrix_transpose.cu)
target_link_libraries(${MODULE}_transpose_demo PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_transpose_demo)
endif()

add_executable(${MODULE}_convolution_demo part_specific/convolution_1d.cu)
target_link_libraries(${MODULE}_convolution_demo PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_convolution_demo)
endif()

add_executable(${MODULE}_reduction_demo part_specific/reduction.cu)
target_link_libraries(${MODULE}_reduction_demo PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_reduction_demo)
endif()

add_executable(${MODULE}_stencil_demo part_specific/stencil_1d.cu)
target_link_libraries(${MODULE}_stencil_demo PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_stencil_demo)
endif()

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
