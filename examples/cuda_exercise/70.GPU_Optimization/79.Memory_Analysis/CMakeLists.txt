project(79_Memory_Analysis CUDA CXX)
set(MODULE ${PROJECT_NAME})

find_package(CUDAToolkit REQUIRED)

# Check for NVML
find_library(NVML_LIB nvidia-ml PATHS ${CUDAToolkit_LIBRARY_DIR} /usr/lib/x86_64-linux-gnu)

add_library(${MODULE}_lib STATIC
    src/profiling/memory_profiler.cu
    src/profiling/bandwidth_test.cu
    src/optimizations/memory_pool.cu
)

if(NVML_LIB)
    target_sources(${MODULE}_lib PRIVATE src/tools/nvml_wrapper.cu)
    target_compile_definitions(${MODULE}_lib PUBLIC HAS_NVML=1)
    target_link_libraries(${MODULE}_lib PUBLIC ${NVML_LIB})
endif()

target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src)
target_link_libraries(${MODULE}_lib PUBLIC CudaCustomLib ${CUDA_BASIC_LIB})

if(BUILD_TESTING)
    add_executable(${MODULE}_test
        test/unit/test_memory_profiler.cu
        test/unit/test_bandwidth.cu
        test/unit/test_memory_pool.cu
    )
    target_link_libraries(${MODULE}_test PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB} ${GTEST_BASIC_LIB})
    gtest_discover_tests(${MODULE}_test)
    add_profiling_targets(${MODULE}_test)
endif()
add_doxygen_target(MODULE_NAME ${MODULE} DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in)
