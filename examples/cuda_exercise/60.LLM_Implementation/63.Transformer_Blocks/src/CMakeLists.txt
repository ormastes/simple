# Source library for Transformer Blocks
add_library(${MODULE}_lib STATIC
    # Normalization kernels
    kernels/layer_norm.cu
    kernels/rms_norm.cu

    # Feed-forward network
    kernels/feed_forward.cu

    # Complete transformer block
    kernels/transformer_block.cu
)

# Export src/ as PUBLIC so both the library's own sources and tests can include headers
target_include_directories(${MODULE}_lib
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}  # Allows kernels/ to include common/*.h, and tests too
)

# Link dependencies (automatically propagates their include paths)
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib  # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
    62_Attention_Mechanisms_lib
)

# Doxygen documentation (Module 16+ requirement)
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
