project(32_cuFFT CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 32 uses Module 16+ format with proper src/ and test/ structure
# Contains cuFFT Fast Fourier Transform library demonstrations

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
