# Dynamic Parallelism

**Tier:** 3 (Skip)
**Status:** Not applicable to Simple

## Why Skipped

Dynamic parallelism is a CUDA-specific hardware feature that allows GPU kernels to
launch child kernels directly from the device. This is tightly coupled to NVIDIA's
GPU execution model and has no direct equivalent in Simple's GPU abstraction.

In Simple, equivalent functionality is achieved through:
- **Host-side dispatch:** The CPU orchestrates kernel launches based on data-dependent decisions
- **Persistent kernels:** Long-running kernels with work queues instead of recursive launches
- **Compute graphs:** Pre-built execution graphs that handle dynamic workloads

## Original CUDA Exercise

See the original CUDA dynamic parallelism exercise for the NVIDIA-specific implementation
using `cudaLaunchDevice()` from within device code.

**Reference:** [NVIDIA CUDA Dynamic Parallelism](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#cuda-dynamic-parallelism)
