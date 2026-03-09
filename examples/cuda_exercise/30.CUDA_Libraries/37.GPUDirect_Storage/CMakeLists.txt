project(37_GPUDirect_Storage CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 37: GPUDirect Storage requires cuFile library and compatible hardware
# Demonstrates direct NVMe-to-GPU data transfers bypassing CPU

add_subdirectory(src)
add_subdirectory(test)
