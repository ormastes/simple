project(24_Memory_Coalescing_And_Bank_Conflicts CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 24 uses Module 16+ format with proper src/ and test/ structure
# Demonstrates memory coalescing and bank conflict optimization techniques

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
