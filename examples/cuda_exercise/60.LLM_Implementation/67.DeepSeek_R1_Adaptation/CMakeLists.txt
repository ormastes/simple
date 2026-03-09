project(67_DeepSeek_R1_Adaptation CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 67: DeepSeek R1 Adaptation
# Implements GQA, RoPE, and SwiGLU components from the DeepSeek R1 architecture.
# Extends Module 62 attention mechanisms with grouped query attention,
# rotary position embeddings, and SwiGLU feed-forward networks.

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
