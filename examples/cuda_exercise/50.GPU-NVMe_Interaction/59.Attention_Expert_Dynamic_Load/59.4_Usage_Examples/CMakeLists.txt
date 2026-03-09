project(59_4_Usage_Examples CUDA CXX)
set(MODULE ${PROJECT_NAME})

add_library(${MODULE}_lib
    src/host/example_registry.cpp
    src/part_specific/example_formatter.cpp
    src/kernels/example_kernel.cu
)

target_include_directories(${MODULE}_lib
    PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}/src/common
)

target_link_libraries(${MODULE}_lib
    PUBLIC
        59_3_Build_and_Install_lib
        ${CUDA_BASIC_LIB}
)

target_compile_features(${MODULE}_lib PUBLIC cxx_std_20)

add_executable(${MODULE}_cli src/host/example_cli.cpp)
target_link_libraries(${MODULE}_cli PRIVATE ${MODULE}_lib)
add_profiling_targets(${MODULE}_cli)

add_executable(${MODULE}_unit_common
    test/unit/common/test_example_registry.cpp
)
target_link_libraries(${MODULE}_unit_common PRIVATE
    ${MODULE}_lib
    ${GTEST_BASIC_LIB}
)
gtest_discover_tests(${MODULE}_unit_common)
add_profiling_targets(${MODULE}_unit_common)

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in
)
