project(46_Virtual_Memory CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 46 - Virtual_Memory
# Module 16+ format with proper src/ and test/ structure

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
