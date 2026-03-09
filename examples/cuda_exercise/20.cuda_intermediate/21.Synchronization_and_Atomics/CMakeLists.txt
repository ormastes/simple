project(21_Synchronization_And_Atomics CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 21 uses Module 16+ format with proper src/ and test/ structure
# Contains synchronization primitives, atomic operations, and lock-free algorithms

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
