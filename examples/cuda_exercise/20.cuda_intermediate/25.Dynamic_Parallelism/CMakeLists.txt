project(25_Dynamic_Parallelism CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 25 uses Module 16+ format with proper src/ and test/ structure
# Demonstrates dynamic parallelism for recursive and adaptive algorithms

# Note: Dynamic parallelism requires special compilation flags
# Enable relocatable device code for this project
set(CMAKE_CUDA_SEPARABLE_COMPILATION ON)
set(CMAKE_CUDA_FLAGS "${CMAKE_CUDA_FLAGS} -rdc=true")

# Build demonstrations from src/
add_subdirectory(src)

# Build tests
if(BUILD_TESTING)
    add_subdirectory(test)
endif()
