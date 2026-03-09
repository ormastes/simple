project(49_Zstd_Compression CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 49 - Zstd_Compression
# Module 16+ format with proper src/ and test/ structure

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
