project(44_CUDA_Graphs CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 44 - CUDA_Graphs
# Module 16+ format with proper src/ and test/ structure

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
