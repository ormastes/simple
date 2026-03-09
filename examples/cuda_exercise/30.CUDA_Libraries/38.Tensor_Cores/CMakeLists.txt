project(38_Tensor_Cores CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 38: Tensor Cores requires compute capability 7.0+

add_subdirectory(src)
add_subdirectory(test)
