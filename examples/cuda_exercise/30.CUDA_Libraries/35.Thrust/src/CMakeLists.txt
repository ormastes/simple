add_executable(${MODULE}_thrust_basics thrust_basics.cu)
target_link_libraries(${MODULE}_thrust_basics PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB}
)
add_profiling_targets(${MODULE}_thrust_basics)

add_executable(${MODULE}_thrust_algorithms thrust_algorithms.cu)
target_link_libraries(${MODULE}_thrust_algorithms PRIVATE
    CudaCustomLib ${CUDA_BASIC_LIB}
)
add_profiling_targets(${MODULE}_thrust_algorithms)

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
