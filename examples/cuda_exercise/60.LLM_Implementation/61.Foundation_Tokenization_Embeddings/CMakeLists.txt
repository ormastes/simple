project(61_Foundation_Tokenization_Embeddings CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 61: Foundation - Tokenization and Embeddings
# Implements tokenizers and embedding layers for transformer input processing
# Based on "LLMs from Scratch" Chapter 2

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
