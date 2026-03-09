# Module 69: MoE NVMe Complete System

## Overview

This capstone module integrates Mixture of Experts (MoE) with NVMe-based expert loading to build a complete LLM inference system. It brings together components from across the 60.LLM_Implementation series -- attention, transformer blocks, MoE routing -- and adds NVMe offloading so that models with more experts than GPU memory can allow are served efficiently.

The system provides a stable C API for model lifecycle management and autoregressive text generation.

## Architecture

### Expert Cache Manager (common/)
- **ExpertCacheManager**: LRU cache keeping hot experts in GPU memory
- **ExpertCacheConfig**: Configuration for cache size, expert count, NVMe enablement

### NVMe Expert Storage (common/)
- **NVMeExpertStorage**: File-based backend for reading/writing expert weights on NVMe
- Supports pinned-memory staging for efficient GPU transfers

### Attention Similarity (kernels/)
- Cosine similarity between hidden states and expert centroids
- Top-k expert prediction for prefetching

### Quantization (kernels/)
- Per-channel INT8 quantization for 4x compression
- Quantize/dequantize roundtrip with bounded error

### Pipeline Management (kernels/)
- **DoublePipeline**: Double-buffered loading and computation
- Overlaps NVMe reads with GPU kernel execution
- Weighted accumulation of expert outputs

### C API (host/)
- `llm_create_model()` / `llm_destroy_model()` lifecycle
- `llm_generate()` autoregressive generation
- Model info queries (vocab size, parameters, max sequence length)

## Key APIs

### C API

- @ref llm_create_model() - Initialize model from config
- @ref llm_generate() - Autoregressive text generation
- @ref llm_destroy_model() - Free all resources
- @ref llm_get_vocab_size(), @ref llm_get_max_seq_len(), @ref llm_get_num_parameters()

### Expert Management

- @ref llm::ExpertCacheManager::init() - Initialize LRU cache
- @ref llm::ExpertCacheManager::get_expert() - Retrieve expert (loads on miss)
- @ref llm::NVMeExpertStorage::load_expert() - NVMe-to-GPU transfer
- @ref llm::compute_expert_similarity() - Cosine similarity for prefetching
- @ref llm::predict_experts() - Top-k expert selection

### Quantization

- @ref llm::quantize_fp32_to_int8() - Per-channel FP32 to INT8
- @ref llm::dequantize_int8_to_fp32() - INT8 back to FP32

## Usage Examples

### Text Generation

```cpp
#include "common/llm_api.h"

LLMModel model = llm_create_model("config.txt");
int input[] = {1, 42, 100};
int output[50];
int n = llm_generate(model, input, 3, output, 50);
llm_destroy_model(model);
```

### Expert Cache

```cpp
#include "common/expert_cache_manager.h"

llm::ExpertCacheConfig cfg = {64, 8, 4*1024*1024, true};
llm::ExpertCacheManager cache;
cache.init(cfg);
float* weights = cache.get_expert(42, stream);
cache.print_stats();
cache.destroy();
```

## Testing

Unit tests cover all major components:
- `test_c_api.cpp` - Model lifecycle and generation
- `test_similarity.cu` - Cosine similarity vs CPU reference
- `test_quantize.cu` - INT8 quantize/dequantize roundtrip
- `test_pipeline.cu` - Double-buffer scheduling and expert accumulation

## Performance

Expected characteristics:

| Component | Operation | Typical Latency |
|-----------|-----------|-----------------|
| Expert Cache (hit) | GPU buffer lookup | <1 us |
| Expert Cache (miss) | NVMe load + cache | ~100 us (PCIe 4.0) |
| Cosine Similarity | 128-dim, 64 experts | ~10 us |
| INT8 Quantization | 16 channels x 256 | ~5 us |
| Pipeline Overlap | Double-buffer swap | ~1 us overhead |

## References

- [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Base reference
- [DeepSeek MoE Paper](https://arxiv.org/abs/2401.06066) - Mixture of Experts architecture
- [GPUDirect Storage](https://developer.nvidia.com/gpudirect-storage) - Direct NVMe-GPU transfers
- [CUDA Streams Best Practices](https://docs.nvidia.com/cuda/cuda-c-best-practices-guide/) - Pipeline scheduling
