# Source library and demos for cuFFT module

# Demo executables demonstrating cuFFT features
add_executable(${MODULE}_fft_1d_demo fft_1d_demo.cu)
target_link_libraries(${MODULE}_fft_1d_demo PRIVATE
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    CUDA::cufft
)
add_profiling_targets(${MODULE}_fft_1d_demo)

add_executable(${MODULE}_fft_2d_demo fft_2d_demo.cu)
target_link_libraries(${MODULE}_fft_2d_demo PRIVATE
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    CUDA::cufft
)
add_profiling_targets(${MODULE}_fft_2d_demo)

add_executable(${MODULE}_fft_batched batched_fft.cu)
target_link_libraries(${MODULE}_fft_batched PRIVATE
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    CUDA::cufft
)
add_profiling_targets(${MODULE}_fft_batched)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
