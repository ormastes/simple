cmake_minimum_required(VERSION 3.18 FATAL_ERROR)

project(53_NVMe_VFIO_Host_Layer CXX)
set(MODULE ${PROJECT_NAME})

# Part 53 uses Module 16+ format with proper src/ and test/ structure
# Contains NVMe VFIO host layer implementations
# Also hosts daemon/ and driver/ components (used by module 56 via symlinks)

# Testing utilities (provided by top-level toolchain)
include(GoogleTest)

# Import profiling targets from cmake utilities
include(${CMAKE_SOURCE_DIR}/00.cmake_lib/inspect_profile.cmake)

# Build libraries from src/
add_subdirectory(src)

# Build daemon (moved from module 56)
add_subdirectory(daemon)

# Build tests from test/
add_subdirectory(test)
