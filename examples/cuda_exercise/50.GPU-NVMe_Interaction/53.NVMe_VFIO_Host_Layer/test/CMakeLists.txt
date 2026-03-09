# Module 53 Tests and Demos

# Device Information Demo
add_executable(device_info_demo
  device_info_demo.cpp
)

target_link_libraries(device_info_demo PRIVATE
  device_detector
  ${CUDA_BASIC_LIB}
)

# Add profiling targets
add_profiling_targets(device_info_demo)

message(STATUS "Module 53 Tests:")
message(STATUS "  - device_info_demo: Device feature detection demo")

# Shared helper libraries (device chooser, setup helper, etc.)
add_subdirectory(helper)

# Helper-level unit tests
add_subdirectory(helper_test)

# Unit tests (MANDATORY from Module 16+)
add_subdirectory(unit)

# System-level IO tests (VFIO hardware required)
add_subdirectory(system_test)

# Utility programs (DBC detection, etc.)
add_subdirectory(util)

# Module 56 GPU queue tests (shared implementation)
if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/module56_gpu_queue)
    add_subdirectory(module56_gpu_queue)
endif()

# Performance tests (Mode comparisons with GPU processing)
if(EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/performance_test)
    add_subdirectory(performance_test)
endif()
