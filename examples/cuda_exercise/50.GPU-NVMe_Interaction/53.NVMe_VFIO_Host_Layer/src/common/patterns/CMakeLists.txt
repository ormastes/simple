# Data Pattern Generation Library
# Provides pattern generation and verification for I/O testing

add_library(nvme_patterns STATIC
    data_patterns.cpp
)

target_include_directories(nvme_patterns PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/../..  # src/ directory
)

target_link_libraries(nvme_patterns PUBLIC
    ${CUDA_BASIC_LIB}
)

set_target_properties(nvme_patterns PROPERTIES
    LINKER_LANGUAGE CXX
    CUDA_RESOLVE_DEVICE_SYMBOLS OFF
    CUDA_SEPARABLE_COMPILATION OFF
)

# Apply coverage flags if enabled
if(ENABLE_COVERAGE)
    target_compile_options(nvme_patterns PRIVATE ${COVERAGE_COMPILE_FLAGS})
endif()
