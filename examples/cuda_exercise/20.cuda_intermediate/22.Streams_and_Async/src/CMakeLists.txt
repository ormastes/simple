# Source library for streams and async operations
# Includes only reusable kernels (part_specific files are separate executables)
add_library(${MODULE}_lib STATIC
    # Reusable stream-optimized kernels
    kernels/matrix_multiply_streams.cu
    kernels/vector_ops_streams.cu
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

# Example executables demonstrating streaming patterns
add_executable(${MODULE}_basic_demo part_specific/basic_streams.cu)
target_link_libraries(${MODULE}_basic_demo PRIVATE ${CUDA_BASIC_LIB})
add_profiling_targets(${MODULE}_basic_demo)

add_executable(${MODULE}_overlap_demo part_specific/overlap_transfer_compute.cu)
target_link_libraries(${MODULE}_overlap_demo PRIVATE ${CUDA_BASIC_LIB})
add_profiling_targets(${MODULE}_overlap_demo)

add_executable(${MODULE}_pipeline_demo part_specific/multi_stream_pipeline.cu)
target_link_libraries(${MODULE}_pipeline_demo PRIVATE ${CUDA_BASIC_LIB})
add_profiling_targets(${MODULE}_pipeline_demo)

add_executable(${MODULE}_callback_demo part_specific/stream_callback.cu)
target_link_libraries(${MODULE}_callback_demo PRIVATE ${CUDA_BASIC_LIB})
add_profiling_targets(${MODULE}_callback_demo)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
