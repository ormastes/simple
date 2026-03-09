project(45_CUDA_IPC CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 45 - CUDA_IPC
# Module 16+ format with proper src/ and test/ structure

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
