project(80_Transformer)

# 80.Transformer - Low-level CUDA kernels for transformer inference
# Build order respects dependencies (common APIs first, then computation modules)

# Common API modules (no inter-dependencies)
add_subdirectory(89.Tensor_Ops_Common_API)
add_subdirectory(88.Normalization_Common_API)
add_subdirectory(87.Attention_Common_API)

# Core GEMM backends (depends on common APIs)
add_subdirectory(86.Core_Common_API)

# Computation modules (depend on common APIs + core)
add_subdirectory(81.Core_GEMM_Operations)
add_subdirectory(84.Normalization)
add_subdirectory(85.Tensor_Operations)
add_subdirectory(83.MLP)
add_subdirectory(82.Attention_Kernels)
