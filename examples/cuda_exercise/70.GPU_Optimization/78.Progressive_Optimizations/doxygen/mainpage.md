# Module 78: Progressive Optimizations

## Overview

This module demonstrates progressive GPU kernel optimization through five matmul stages,
three backpropagation stages, and three attention stages. Each stage builds on the previous,
showing how specific techniques (shared memory, tiling, vectorization, Tensor Cores, kernel
fusion, FlashAttention) improve performance while maintaining correctness.

## Module Architecture

The module is organized into three optimization progressions:

- **matmul/**: Matrix multiplication stages from naive to Tensor Core WMMA
  - `01_naive.cu` - Baseline: one thread per element (~50 GFLOPS)
  - `02_shared_memory.cu` - 16x16 shared memory tiling (~200 GFLOPS)
  - `03_tiled.cu` - 32x32 tiles with register blocking (~500 GFLOPS)
  - `04_vectorized.cu` - float4 vectorized loads, 2D register tiles (~800 GFLOPS)
  - `05_wmma.cu` - Tensor Core WMMA, fp16 inputs, fp32 accumulation (~1200+ GFLOPS)

- **backprop/**: Backpropagation optimization for fully-connected layers
  - `01_naive.cu` - Separate kernels for grad_input, grad_weight, grad_bias
  - `02_fused.cu` - Fused forward+backward, fewer kernel launches
  - `03_optimized.cu` - Shared memory tiling and vectorized loads

- **attention/**: Scaled dot-product attention optimization
  - `01_naive.cu` - Full NxN matrix materialization, separate softmax
  - `02_tiled.cu` - Shared memory tiling for QK^T and attention*V
  - `03_flash_v2.cu` - FlashAttention v2: online softmax, O(N) memory

- **python/**: Analysis and visualization scripts
  - `benchmark_all.py` - Run all stages and collect timing data
  - `visualize.py` - Bar charts comparing optimization stages
  - `roofline.py` - Roofline model analysis

## Key Components

### Matmul API

All matmul stages share a consistent interface in namespace `opt78`:
```cpp
void matmul_<stage>(float* C, const float* A, const float* B,
                    int M, int N, int K, cudaStream_t s = 0);
```

### Backprop API

```cpp
void backprop_<stage>(float* grad_input, float* grad_weight, float* grad_bias,
                      const float* grad_output, const float* input,
                      const float* weight, int batch, int in_features,
                      int out_features, cudaStream_t s = 0);
```

### Attention API

```cpp
void attention_<stage>(float* output, [float* scores_buf,]
                       const float* Q, const float* K, const float* V,
                       int batch, int seq_len, int head_dim,
                       cudaStream_t s = 0);
```

## Usage Examples

See the `test/unit/` directory for comprehensive usage:
- `test_matmul_stages.cu` - Correctness and consistency across all five stages
- `test_backprop_stages.cu` - Gradient verification for naive, fused, and optimized
- `test_attention_stages.cu` - CPU reference comparison for all attention stages

## Building Documentation

From the build directory:
```bash
ninja doxygen_78_Progressive_Optimizations
```

## Performance Considerations

| Stage | Technique | Expected GFLOPS | Key Optimization |
|-------|-----------|----------------|------------------|
| Naive | 1 thread/element | ~50 | Baseline |
| Shared Memory | 16x16 tiles | ~200 | Data reuse |
| Tiled | 32x32 + registers | ~500 | Arithmetic intensity |
| Vectorized | float4 + 8x8 tiles | ~800 | Memory throughput |
| WMMA | Tensor Cores | ~1200+ | Hardware acceleration |

## See Also

- Module README.md for detailed learning materials
- Module 79 (Memory_Analysis) for memory profiling and bandwidth analysis
