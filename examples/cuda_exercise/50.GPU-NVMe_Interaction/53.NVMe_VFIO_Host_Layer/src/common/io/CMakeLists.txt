# NVMe I/O Utilities Library
# Provides file LBA mapping and physical block operations

add_library(nvme_io_utils STATIC
    nvme_file_utils.cpp
)

target_include_directories(nvme_io_utils PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/../..  # src/ directory
)

target_link_libraries(nvme_io_utils PUBLIC
    ${CUDA_BASIC_LIB}
)

set_target_properties(nvme_io_utils PROPERTIES
    LINKER_LANGUAGE CXX
    CUDA_RESOLVE_DEVICE_SYMBOLS OFF
    CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled
if(ENABLE_COVERAGE)
    target_compile_options(nvme_io_utils PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()
