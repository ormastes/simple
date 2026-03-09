project(23_Shared_Memory CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 23 uses Module 16+ format with proper src/ and test/ structure
# Contains shared memory patterns: tiling, reduction, transpose, convolution

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
