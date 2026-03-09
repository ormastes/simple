project(65_Training_Infrastructure CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 65: Training Infrastructure
# Implements optimizer, learning rate scheduler, loss functions, and gradient utilities
# for end-to-end LLM training on GPU.

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
