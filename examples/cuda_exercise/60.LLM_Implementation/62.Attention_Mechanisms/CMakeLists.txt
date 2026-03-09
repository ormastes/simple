project(62_Attention_Mechanisms CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 62: Attention Mechanisms
# Implements self-attention, causal attention, and multi-head attention
# for transformer-based language models.
# Based on "LLMs from Scratch" Chapter 3

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
