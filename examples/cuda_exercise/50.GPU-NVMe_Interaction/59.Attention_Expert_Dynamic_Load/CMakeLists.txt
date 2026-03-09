project(59_Attention_Expert_Dynamic_Load CUDA CXX)
set(MODULE ${PROJECT_NAME})

# Core library and optional bindings
add_subdirectory(src)

# Documentation-backed overview module
add_subdirectory(59.1_Overview)
add_subdirectory(59.2_Features)
add_subdirectory(59.3_Build_and_Install)
add_subdirectory(59.4_Usage_Examples)
add_subdirectory(59.5_PyTorch_Integration)
add_subdirectory(59.6_Dynamic_NVMe_Loading)
add_subdirectory(59.7_Performance)
add_subdirectory(59.8_Testing)
add_subdirectory(59.9_NVMe_Data_Loading)

# Integration tests (Python-based)
add_subdirectory(test)

# Doxygen documentation (Module 16+ requirement)
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/doxygen/Doxyfile.in
)
