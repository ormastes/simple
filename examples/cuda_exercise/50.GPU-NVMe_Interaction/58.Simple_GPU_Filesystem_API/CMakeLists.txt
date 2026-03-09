project(58_Simple_Filesystem_Layer CXX)
set(MODULE ${PROJECT_NAME})

# Part 58: Simple Filesystem Layer for NVMe
# Provides node-based LBA management with file operations, GC, and C API

# Build libraries from src/
add_subdirectory(src)

# Build tests from test/
add_subdirectory(test)
