project(48_Tile_Based_Programming CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 48 - Tile_Based_Programming
# Module 16+ format with proper src/ and test/ structure

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
