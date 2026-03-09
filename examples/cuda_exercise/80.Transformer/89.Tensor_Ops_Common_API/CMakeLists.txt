project(89_Tensor_Ops_Common_API CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 89 - Tensor_Ops_Common_API
# Module 16+ format with proper src/ and test/ structure

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
