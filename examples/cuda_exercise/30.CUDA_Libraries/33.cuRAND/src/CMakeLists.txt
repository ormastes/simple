# cuRAND demo executables

add_executable(${MODULE}_curand_host_demo curand_host_demo.cu)
target_link_libraries(${MODULE}_curand_host_demo PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} CUDA::curand
)
add_profiling_targets(${MODULE}_curand_host_demo)

add_executable(${MODULE}_curand_device_demo curand_device_demo.cu)
target_link_libraries(${MODULE}_curand_device_demo PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} CUDA::curand
)
add_profiling_targets(${MODULE}_curand_device_demo)

add_executable(${MODULE}_monte_carlo_pi monte_carlo_pi.cu)
target_link_libraries(${MODULE}_monte_carlo_pi PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB} CUDA::curand
)
add_profiling_targets(${MODULE}_monte_carlo_pi)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
