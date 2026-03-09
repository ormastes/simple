project(41_Advanced_PTX_Assembly CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 41 uses Module 16+ format with proper src/ and test/ structure
# Advanced PTX Assembly - low-level GPU programming with inline PTX

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
