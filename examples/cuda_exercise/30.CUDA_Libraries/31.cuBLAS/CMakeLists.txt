project(31_cuBLAS CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 31 demonstrates cuBLAS library usage
# Contains examples of Level 1, 2, 3 BLAS operations and batched operations

# Build libraries and demos from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
