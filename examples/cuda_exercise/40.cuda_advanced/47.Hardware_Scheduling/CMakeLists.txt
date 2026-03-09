project(47_Hardware_Scheduling CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Part 47 uses Module 16+ format with proper src/ and test/ structure
# Contains hardware scheduling and occupancy optimization implementations

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
