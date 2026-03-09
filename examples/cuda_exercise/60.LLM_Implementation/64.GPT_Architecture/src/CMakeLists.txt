# Source library for GPT Architecture
add_library(${MODULE}_lib STATIC
    kernels/gpt_model.cu
    kernels/sampling.cu
    kernels/text_generator.cu
)

# Export src/ so tests and downstream modules can include headers
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

# Enable --extended-lambda for device lambdas in CUDA code
target_compile_options(${MODULE}_lib PRIVATE $<$<COMPILE_LANGUAGE:CUDA>:--extended-lambda>)

# Link dependencies (automatically propagates their include paths)
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib ${CUDA_BASIC_LIB}
    63_Transformer_Blocks_lib
)

# Doxygen documentation (Module 16+ requirement)
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
