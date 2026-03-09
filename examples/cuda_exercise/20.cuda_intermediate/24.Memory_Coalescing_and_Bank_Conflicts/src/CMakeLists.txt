# Reusable optimized kernels library (improved versions from module 23)
add_library(${MODULE}_lib STATIC
    kernels/matrix_multiply.cu
    kernels/vector_ops.cu
)

# Export src/ as INTERFACE so tests can include kernel source files
target_include_directories(${MODULE}_lib
    INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}
)

# Link dependencies
target_link_libraries(${MODULE}_lib PUBLIC
    CudaCustomLib
    ${CUDA_BASIC_LIB}
)

# Demo executables demonstrating memory coalescing and bank conflicts

# Coalescing demonstration
add_executable(${MODULE}_coalescing_demo part_specific/coalescing_demo.cu)
target_link_libraries(${MODULE}_coalescing_demo PRIVATE ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_coalescing_demo)
endif()
if(COMMAND add_coalescing_analysis)
    add_coalescing_analysis(${MODULE}_coalescing_demo)
endif()

# Bank conflicts demonstration
add_executable(${MODULE}_bank_conflicts part_specific/bank_conflicts.cu)
target_link_libraries(${MODULE}_bank_conflicts PRIVATE ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_bank_conflicts)
endif()

# AoS vs SoA comparison
add_executable(${MODULE}_aos_vs_soa part_specific/aos_vs_soa.cu)
target_link_libraries(${MODULE}_aos_vs_soa PRIVATE ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_aos_vs_soa)
endif()

# Memory access patterns analysis
add_executable(${MODULE}_memory_patterns part_specific/memory_patterns.cu)
target_link_libraries(${MODULE}_memory_patterns PRIVATE ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_memory_patterns)
endif()
if(COMMAND add_coalescing_analysis)
    add_coalescing_analysis(${MODULE}_memory_patterns)
endif()

# Comparison demo (Module 23 vs Module 24)
add_executable(${MODULE}_coalescing_comparison part_specific/coalescing_comparison.cu)
target_link_libraries(${MODULE}_coalescing_comparison PRIVATE ${MODULE}_lib ${CUDA_BASIC_LIB})
if(COMMAND add_profiling_targets)
    add_profiling_targets(${MODULE}_coalescing_comparison)
endif()

# ============================================================================
# Doxygen Documentation (Module 16+ requirement)
# ============================================================================

# Use shared Doxygen function from 00.cmake_lib
add_doxygen_target(
    MODULE_NAME ${MODULE}
    DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/../doxygen/Doxyfile.in
)
