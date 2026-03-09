# Common utilities library for Module 59
# Eliminates code duplication across all 9 submodules

add_library(module59_common_utils STATIC
    kernel_utils.cu
)

target_include_directories(module59_common_utils PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
)

target_link_libraries(module59_common_utils
    PUBLIC
        ${CUDA_BASIC_LIB}
)

target_compile_features(module59_common_utils PUBLIC cxx_std_20)

# Install headers for other modules to use
install(FILES
    cli_template.h
    formatter_template.h
    data_structure_base.h
    kernel_utils.h
    test_template.h
    DESTINATION include/module59/common_utils
)