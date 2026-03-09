# add interface target
add_library(GTestCudaGenerator INTERFACE)
target_include_directories(GTestCudaGenerator
INTERFACE
    ${CMAKE_CURRENT_LIST_DIR}
)

add_library(GTestCudaMain STATIC
    gpu_gtest.cpp
)
target_link_libraries(GTestCudaMain
PUBLIC
    GTest::gtest 
    GTest::gmock
    GTestCudaGenerator
    CudaCustomLib
)
