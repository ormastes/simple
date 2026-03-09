project(64_GPT_Architecture CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 64: GPT Architecture
# Implements the complete GPT model: configuration presets, forward pass,
# sampling strategies, and autoregressive text generation.
# Based on "LLMs from Scratch" Chapter 4-5

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
