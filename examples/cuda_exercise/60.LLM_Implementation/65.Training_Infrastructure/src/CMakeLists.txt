# Source library for Training Infrastructure
add_library(${MODULE}_lib STATIC
    # Host-side training orchestration
    host/training_loop.cpp
    host/adamw_optimizer.cpp
    host/lr_scheduler.cpp

    # CUDA kernel implementations
    kernels/adamw_kernel.cu
    kernels/loss_kernels.cu
    kernels/gradient_kernels.cu
)

# Export src/ as PUBLIC so both library sources and tests can include headers
target_include_directories(${MODULE}_lib
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}  # Allows library sources and tests to include common/*.h
)

# Link dependencies (automatically propagates their include paths)
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib  # Provides cuda_utils.h
    ${CUDA_BASIC_LIB}
    64_GPT_Architecture_lib
)

# Doxygen documentation (Module 16+ requirement)
# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
