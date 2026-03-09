cmake_path(GET CMAKE_CURRENT_SOURCE_DIR FILENAME ProjectName)
project(${ProjectName})

add_library(${PROJECT_NAME}_lib STATIC kernel.cu)
target_link_libraries(${PROJECT_NAME}_lib PUBLIC CUDA::cudart)

add_executable(${PROJECT_NAME} src.cpp)
target_link_libraries(${PROJECT_NAME} PRIVATE ${PROJECT_NAME}_lib)

# Tests
add_executable(${PROJECT_NAME}_test test_kernel.cpp)
target_link_libraries(${PROJECT_NAME}_test PRIVATE
    ${PROJECT_NAME}_lib
    GTest::gtest_main
)

# Register test with CTest
include(GoogleTest)
gtest_discover_tests(${PROJECT_NAME}_test)
