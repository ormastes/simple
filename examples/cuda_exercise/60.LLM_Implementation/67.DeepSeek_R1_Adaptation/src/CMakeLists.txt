# Source library for DeepSeek R1 Adaptation
add_library(${MODULE}_lib STATIC
    # Host-side checkpoint loading
    host/deepseek_loader.cpp

    # CUDA kernel implementations
    kernels/gqa_attention.cu
    kernels/rope_fused.cu
    kernels/swiglu_fused.cu
)

# Export src/ as PUBLIC so tests and downstream modules can include headers
target_include_directories(${MODULE}_lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

# Link dependencies (automatically propagates their include paths)
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib      # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
    62_Attention_Mechanisms_lib
)

# Doxygen documentation (Module 16+ requirement)
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
