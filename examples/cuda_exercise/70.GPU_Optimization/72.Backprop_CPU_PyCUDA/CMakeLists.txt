project(72_Backprop_CPU_PyCUDA)
set(MODULE ${PROJECT_NAME})

# Find required packages
find_package(CUDAToolkit REQUIRED)
find_package(Threads REQUIRED)
find_package(OpenMP)

if(OpenMP_CXX_FOUND)
    message(STATUS "OpenMP found: ${OpenMP_CXX_VERSION}")
    set(HAS_OPENMP ON)
else()
    message(STATUS "OpenMP not found. Multi-threaded implementations will be disabled.")
    set(HAS_OPENMP OFF)
endif()

# Find Python for PyCUDA wrappers
find_package(Python3 COMPONENTS Interpreter Development)

# Source files
set(CPU_BACKPROP_SOURCES
    src/kernels/cpu_backprop.cu
)

# Create library
add_library(${PROJECT_NAME}_lib ${CPU_BACKPROP_SOURCES})

target_include_directories(${PROJECT_NAME}_lib PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/src/kernels
    ${CUDAToolkit_INCLUDE_DIRS}
)

target_link_libraries(${PROJECT_NAME}_lib PUBLIC
    CUDA::cudart
    ${CUDA_BASIC_LIB}
    Threads::Threads
)

if(HAS_OPENMP)
    target_link_libraries(${PROJECT_NAME}_lib PUBLIC OpenMP::OpenMP_CXX)
    target_compile_definitions(${PROJECT_NAME}_lib PUBLIC HAS_OPENMP=1)
endif()

# Compile options
# Note: -march=native enables CPU-specific optimizations for maximum performance
target_compile_options(${PROJECT_NAME}_lib PRIVATE
    $<$<COMPILE_LANGUAGE:CXX>:
        -march=native
    >
)
# Optimization level (-O3) is controlled by CMAKE_BUILD_TYPE globally

# Tests
if(BUILD_TESTING)
    add_executable(${PROJECT_NAME}_test
        test/unit/test_cpu_backprop.cu
        ${CMAKE_SOURCE_DIR}/00.test_lib/gpu_gtest.cpp
    )

    target_link_libraries(${PROJECT_NAME}_test PRIVATE
        ${PROJECT_NAME}_lib
        ${GTEST_BASIC_LIB}
    )

    gtest_discover_tests(${PROJECT_NAME}_test)
endif()

# Python bindings (PyCUDA wrapper)
if(Python3_FOUND)
    # Build shared library for PyCUDA
    add_library(cpu_backprop_py SHARED
        src/kernels/cpu_backprop.cu
    )

    target_link_libraries(cpu_backprop_py
        ${PROJECT_NAME}_lib
        Python3::Python
    )

    set_target_properties(cpu_backprop_py PROPERTIES
        PREFIX ""
        OUTPUT_NAME "libcpu_backprop"
        SUFFIX ".so"
    )

    # Copy Python wrapper to build directory
    add_custom_command(
        TARGET cpu_backprop_py POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_directory
                ${CMAKE_CURRENT_SOURCE_DIR}/src/python
                ${CMAKE_CURRENT_BINARY_DIR}/python
        COMMENT "Copying Python wrapper files"
    )

    # Install Python module
    install(TARGETS cpu_backprop_py
            LIBRARY DESTINATION ${Python3_SITELIB})
    install(DIRECTORY src/python/
            DESTINATION ${Python3_SITELIB}/cpu_backprop
            FILES_MATCHING PATTERN "*.py")
else()
    message(STATUS "Python not found. PyCUDA wrappers will not be built.")
endif()

# Profiling targets
if(TARGET ${PROJECT_NAME}_test)
    add_profiling_targets(${PROJECT_NAME}_test)
endif()

# ---- Doxygen documentation target ----
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in
)
