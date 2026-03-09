project(42_Compiler_Optimizations CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 42 - Compiler_Optimizations
# Module 16+ format with proper src/ and test/ structure

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
