# cuFFT

**Tier:** 3 (Skip)
**Status:** Not applicable to Simple

## Why Skipped

cuFFT is an NVIDIA proprietary library for computing Fast Fourier Transforms on GPU.
It is a closed-source, hardware-specific library that cannot be meaningfully
translated to Simple's GPU abstraction.

For FFT operations in Simple, consider:
- **CPU FFT:** Implement Cooley-Tukey FFT using standard Simple code
- **GPU FFT kernel:** Write a custom FFT kernel using `@gpu_kernel` (for educational purposes)
- **Vendor FFT:** Use Simple's FFI to call platform-appropriate FFT libraries

## Original CUDA Exercise

See the original cuFFT exercise for the NVIDIA-specific implementation using
`cufftPlan1d()`, `cufftExecC2C()`, etc.

**Reference:** [NVIDIA cuFFT Documentation](https://docs.nvidia.com/cuda/cufft/index.html)
