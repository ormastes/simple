project(13_Debugging_CUDA_in_VSCode)

add_executable(${PROJECT_NAME} vector_add_2d.cu)

# Note: This module demonstrates CUDA debugging.
# Build with: cmake -DCMAKE_BUILD_TYPE=Debug -B build
# The Debug build type automatically enables -g, -G, and -O0 globally.
# No module-specific optimization overrides needed.

target_link_libraries(${PROJECT_NAME} CUDA::cudart)