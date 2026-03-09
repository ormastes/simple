project(63_Transformer_Blocks CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 63: Transformer Blocks
# Implements LayerNorm, RMSNorm, Feed-Forward Networks, and complete
# transformer blocks with residual connections for LLM architectures.

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
