# Source library for Simple Filesystem Layer
add_library(${MODULE}_lib STATIC
    host/nvme_simple_fs.cpp
    host/nvme_simple_fs_c_api.cpp
    host/nvme_fs_io_stubs.cpp
)

# Export src/ as INTERFACE for tests to include headers
target_include_directories(${MODULE}_lib
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/common
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}
)

# Link dependencies
target_link_libraries(${MODULE}_lib PUBLIC
    nvme_vio_host
    host_io_host_mem
)

# Doxygen documentation (Module 16+ requirement)
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
