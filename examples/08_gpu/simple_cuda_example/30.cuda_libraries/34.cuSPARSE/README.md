# cuSPARSE

**Tier:** 3 (Skip)
**Status:** Not applicable to Simple

## Why Skipped

cuSPARSE is an NVIDIA proprietary library for sparse matrix operations on GPU. It is
a closed-source, hardware-specific library that cannot be meaningfully translated to
Simple's GPU abstraction.

For sparse matrix operations in Simple, consider:
- **CSR format:** Implement Compressed Sparse Row format with custom `@gpu_kernel` SpMV
- **Dense fallback:** For small-to-medium matrices, dense operations may be sufficient
- **Vendor sparse:** Use Simple's FFI to call platform-appropriate sparse libraries

## Original CUDA Exercise

See the original cuSPARSE exercise for the NVIDIA-specific implementation using
`cusparseCreate()`, `cusparseSpMV()`, etc.

**Reference:** [NVIDIA cuSPARSE Documentation](https://docs.nvidia.com/cuda/cusparse/index.html)
