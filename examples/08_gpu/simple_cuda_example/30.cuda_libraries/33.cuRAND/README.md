# cuRAND

**Tier:** 3 (Skip)
**Status:** Not applicable to Simple

## Why Skipped

cuRAND is an NVIDIA proprietary library for generating random numbers on GPU. It is
a closed-source, hardware-specific library that cannot be meaningfully translated to
Simple's GPU abstraction.

For GPU random number generation in Simple, consider:
- **GPU RNG kernel:** Implement a simple PRNG (e.g., xorshift) as a `@gpu_kernel`
- **Host-side generation:** Generate random data on CPU and transfer to GPU
- **`Tensor.randn()`:** Use Simple's built-in tensor random initialization

## Original CUDA Exercise

See the original cuRAND exercise for the NVIDIA-specific implementation using
`curandCreateGenerator()`, `curandGenerateUniform()`, etc.

**Reference:** [NVIDIA cuRAND Documentation](https://docs.nvidia.com/cuda/curand/index.html)
