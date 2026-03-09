# Source library for GPUDirect Storage
add_library(${MODULE}_lib STATIC
    # cuFile wrapper utilities
    common/cufile_wrapper.cpp
    # GPU pattern generation kernels
    kernels/pattern_generator.cu
)

# Find cuFile library
find_library(CUFILE_LIBRARY cufile
    HINTS
        /usr/local/cuda/lib64
        /usr/lib/x86_64-linux-gnu
        ${CUDA_TOOLKIT_ROOT_DIR}/lib64
        ${CUDA_TOOLKIT_ROOT_DIR}/targets/x86_64-linux/lib
    REQUIRED
)

# Export src/ as INTERFACE so tests can include headers
target_include_directories(${MODULE}_lib
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/common
           ${CMAKE_CURRENT_SOURCE_DIR}/kernels
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}
)

# Link dependencies
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib
    ${CUDA_BASIC_LIB}
    ${CUFILE_LIBRARY}
)

# Display cuFile library location
message(STATUS "cuFile library: ${CUFILE_LIBRARY}")

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
