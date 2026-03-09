project(27_Multi_GPU_Programming CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 27 uses Module 16+ format with proper src/ and test/ structure
# Multi-GPU programming - extends Module 26 cooperative groups to multiple GPUs

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
