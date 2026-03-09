project(22_Streams_And_Async CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 22 uses Module 16+ format with proper src/ and test/ structure
# Contains CUDA streams for concurrent execution and asynchronous operations

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)