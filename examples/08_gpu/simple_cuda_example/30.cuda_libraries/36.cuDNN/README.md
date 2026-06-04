# cuDNN

**Tier:** 3 (Skip)
**Status:** Not applicable to Simple

## Why Skipped

cuDNN is an NVIDIA proprietary deep neural network library providing GPU-accelerated
primitives for convolution, pooling, normalization, and activation. It is a
closed-source, hardware-specific library that cannot be meaningfully translated to
Simple's GPU abstraction.

In Simple, equivalent functionality is provided by:
- **`std.ml` module:** Built-in layer types (Linear, LayerNorm, GELU, etc.)
- **`~>` pipeline:** Composable neural network layers
- **Custom kernels:** `@gpu_kernel` for specialized operations
- See exercises 62-64 (Attention, Transformer Blocks, GPT Architecture) for implementations

## Original CUDA Exercise

See the original cuDNN exercise for the NVIDIA-specific implementation using
`cudnnConvolutionForward()`, `cudnnBatchNormalizationForward()`, etc.

**Reference:** [NVIDIA cuDNN Documentation](https://docs.nvidia.com/deeplearning/cudnn/index.html)
