project(73_Attention_CPU_PyCUDA)
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
set(CPU_ATTENTION_SOURCES
    src/kernels/cpu_attention.cu
)

# Create library
add_library(${PROJECT_NAME}_lib ${CPU_ATTENTION_SOURCES})

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

# Benchmark executable
add_executable(${PROJECT_NAME}_benchmark
    src/benchmark.cu
)

target_link_libraries(${PROJECT_NAME}_benchmark
    PRIVATE
    ${PROJECT_NAME}_lib
    ${CUDA_BASIC_LIB}
)

target_include_directories(${PROJECT_NAME}_benchmark PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/src/kernels
)

# Tests
if(BUILD_TESTING)
    add_executable(${PROJECT_NAME}_test
        test/unit/test_cpu_attention.cu
        ${CMAKE_SOURCE_DIR}/00.test_lib/gpu_gtest.cpp
    )

    target_link_libraries(${PROJECT_NAME}_test
        ${PROJECT_NAME}_lib
        ${GTEST_BASIC_LIB}
        GTest::gtest
        GTestCudaGenerator
    )

    gtest_discover_tests(${PROJECT_NAME}_test)
endif()

# Python bindings (PyCUDA wrapper)
if(Python3_FOUND)
    # Build shared library for PyCUDA
    add_library(cpu_attention_py SHARED
        src/kernels/cpu_attention.cu
    )

    target_link_libraries(cpu_attention_py
        ${PROJECT_NAME}_lib
        Python3::Python
    )

    set_target_properties(cpu_attention_py PROPERTIES
        PREFIX ""
        OUTPUT_NAME "libcpu_attention"
        SUFFIX ".so"
    )

    # Copy Python wrapper to build directory
    add_custom_command(
        TARGET cpu_attention_py POST_BUILD
        COMMAND ${CMAKE_COMMAND} -E copy_directory
                ${CMAKE_CURRENT_SOURCE_DIR}/src/python
                ${CMAKE_CURRENT_BINARY_DIR}/python
        COMMENT "Copying Python wrapper files"
    )

    # Install Python module
    install(TARGETS cpu_attention_py
            LIBRARY DESTINATION ${Python3_SITELIB})
    install(DIRECTORY src/python/
            DESTINATION ${Python3_SITELIB}/cpu_attention
            FILES_MATCHING PATTERN "*.py")
else()
    message(STATUS "Python not found. PyCUDA wrappers will not be built.")
endif()

# Profiling targets
add_profiling_targets(${PROJECT_NAME}_benchmark)

# Custom benchmark target
add_custom_target(benchmark_attention
    COMMAND ${CMAKE_CURRENT_BINARY_DIR}/${PROJECT_NAME}_benchmark
    DEPENDS ${PROJECT_NAME}_benchmark
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    COMMENT "Running CPU Attention benchmarks"
)

# ---- Doxygen documentation target ----
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in
)
