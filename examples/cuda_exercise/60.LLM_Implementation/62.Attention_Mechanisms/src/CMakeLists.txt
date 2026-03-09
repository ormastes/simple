# Source library for Attention Mechanisms
add_library(${MODULE}_lib STATIC
    # Host-side setup and weight management
    host/attention_setup.cpp

    # CUDA kernel implementations
    kernels/attention_naive.cu
    kernels/multi_head_attention.cu
)

# Export src/ as INTERFACE so tests can include headers
target_include_directories(${MODULE}_lib
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}  # Allows library sources and tests to include common/*.h
)

# Link dependencies (automatically propagates their include paths)
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib  # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
)

# Doxygen documentation (Module 16+ requirement)
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
