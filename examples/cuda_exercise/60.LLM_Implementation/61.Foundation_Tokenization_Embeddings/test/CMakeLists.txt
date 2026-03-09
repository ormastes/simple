# Test executables
add_executable(${MODULE}_test
    # Tests for tokenizers (CPU)
    unit/host/test_simple_tokenizer_v1.cpp
    unit/host/test_simple_tokenizer_v2.cpp
    unit/host/test_bpe_tokenizer.cpp

    # Tests for embeddings (GPU)
    unit/kernels/test_token_embedding.cu
    unit/kernels/test_positional_encoding.cu
    unit/kernels/test_embedding_layer.cu
)

# Link to libraries - they carry all necessary include paths
target_link_libraries(${MODULE}_test PRIVATE
    ${MODULE}_lib      # Gets src/ (INTERFACE) for including kernel sources
    ${CUDA_BASIC_LIB}
    ${GTEST_BASIC_LIB} # Gets 00.test_lib path automatically
)

gtest_discover_tests(${MODULE}_test)
add_profiling_targets(${MODULE}_test)
