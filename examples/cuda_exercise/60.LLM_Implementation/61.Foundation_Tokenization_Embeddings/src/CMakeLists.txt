# Source library for Foundation - Tokenization and Embeddings
add_library(${MODULE}_lib STATIC
    # Tokenizers (CPU implementations)
    host/simple_tokenizer_v1.cpp
    host/simple_tokenizer_v2.cpp
    host/bpe_tokenizer.cpp

    # Embedding kernels (GPU implementations)
    kernels/token_embedding.cu
    kernels/positional_encoding.cu
    kernels/embedding_layer.cu
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}  # Allows tests to include kernels/*.cu
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
