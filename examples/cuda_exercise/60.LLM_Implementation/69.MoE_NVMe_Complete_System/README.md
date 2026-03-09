# Part 69: MoE NVMe Complete System
**Goal**: Integrate Mixture of Experts with NVMe-based expert loading into a complete LLM inference system with a stable C API.

This capstone module brings together the components developed throughout the 60.LLM_Implementation series -- tokenization, attention, transformer blocks, MoE routing -- and adds NVMe-backed expert offloading so that models with more experts than fit in GPU memory can be served with minimal latency.

## Project Structure

```
69.MoE_NVMe_Complete_System/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── expert_cache_manager.h    # LRU cache for expert weights
│   │   ├── attention_similarity.h    # Cosine similarity for prefetching
│   │   ├── nvme_expert_storage.h     # NVMe read/write backend
│   │   └── llm_api.h                 # C API declarations
│   ├── host/
│   │   └── c_api.cpp                 # C API implementation
│   └── kernels/
│       ├── similarity_kernels.cu     # GPU cosine similarity
│       ├── quantize_kernels.cu       # INT8 quantization/dequantization
│       └── pipeline_kernels.cu       # Double-buffer pipeline
├── test/
│   ├── CMakeLists.txt
│   └── unit/
│       ├── host/
│       │   └── test_c_api.cpp
│       └── kernels/
│           ├── test_similarity.cu
│           ├── test_quantize.cu
│           └── test_pipeline.cu
└── examples/
    ├── text_generation.cpp           # Text generation demo
    └── question_answering.cpp        # QA with prompt template
```

## Quick Navigation
- [69.1 Expert Cache Manager](#691-expert-cache-manager)
- [69.2 NVMe Expert Storage](#692-nvme-expert-storage)
- [69.3 Attention Similarity](#693-attention-similarity)
- [69.4 Quantization](#694-quantization)
- [69.5 C API](#695-c-api)
- [69.6 Examples](#696-examples)
- [69.7 Summary](#697-summary)
- [Build & Run](#build--run)

---

## **69.1 Expert Cache Manager**
The expert cache manager keeps frequently-used MoE expert weight tensors in GPU memory using an LRU eviction policy, transparently loading uncached experts from NVMe storage on demand.

### **69.1.1 Cache Design**
The cache maps expert IDs to GPU buffer slots. When all slots are full and a new expert is requested, the least recently used slot is evicted.

```cpp
// src/common/expert_cache_manager.h
ExpertCacheConfig config = {64, 8, 4*1024*1024, true};
ExpertCacheManager cache;
cache.init(config);

float* weights = cache.get_expert(42, stream);  // Loads from NVMe if not cached
cache.print_stats();  // Reports hit/miss ratio
cache.destroy();
```

**Key Points**:
- LRU eviction ensures hot experts remain in GPU memory
- Configurable cache size trades GPU memory for hit rate
- Cache statistics help tune `max_cached_experts`

**Source**: `src/common/expert_cache_manager.h`

### **69.1.2 Cache Slot Management**
Each slot holds one expert's weights. The `cache_order` array tracks recency: index 0 is the most recently used. On each access, the slot is promoted to position 0 and all others shift down.

**Key Points**:
- O(max_cached_experts) promotion and eviction
- `in_cache` bitmap enables O(1) hit detection
- `cache_slot_map` provides O(1) expert-to-slot lookup

---

## **69.2 NVMe Expert Storage**
The NVMe storage backend persists expert weights as individual binary files on NVMe devices, enabling models with hundreds of experts to operate within limited GPU memory.

### **69.2.1 Storage Layout**
Each expert is stored as a separate file (`expert_<id>.bin`) for independent access and parallel loading.

```cpp
// src/common/nvme_expert_storage.h
NVMeExpertStorage storage;
storage.init("/mnt/nvme/experts", 64, 4*1024*1024);

float* d_buffer;
cudaMalloc(&d_buffer, 4*1024*1024);
storage.load_expert(d_buffer, 0, stream);
storage.save_expert(d_buffer, 0);
storage.destroy();
```

**Key Points**:
- Per-expert files allow parallel I/O across multiple NVMe devices
- Pinned host memory staging for efficient cudaMemcpyAsync transfers
- Graceful fallback (zero-fill) when expert files are missing

**Source**: `src/common/nvme_expert_storage.h`

### **69.2.2 Transfer Pipeline**
Loading follows a three-stage path: NVMe -> pinned host memory -> GPU buffer. The pinned staging buffer enables asynchronous transfers that overlap with computation.

---

## **69.3 Attention Similarity**
Cosine similarity between the current hidden state and expert centroid vectors predicts which experts a token will need, enabling prefetching from NVMe before the MoE router makes its final decision.

### **69.3.1 Cosine Similarity Kernel**
Each CUDA block handles one expert. Shared memory reduction computes the dot product and centroid norm in parallel.

```cpp
// src/common/attention_similarity.h
compute_expert_similarity(d_similarities, d_hidden_state,
                         d_expert_centroids, d_model, num_experts, stream);
```

**Key Points**:
- One block per expert for full parallelism
- Shared memory reduction avoids global atomics
- Pre-computed hidden state norm avoids redundant work

**Source**: `src/kernels/similarity_kernels.cu`

### **69.3.2 Expert Prediction**
Top-k selection identifies the most likely experts for prefetching. Uses a simple O(num_experts * top_k) algorithm suitable for typical expert counts (8--128).

```cpp
predict_experts(d_predicted, d_similarities, num_experts, top_k, stream);
```

**Source**: `src/kernels/similarity_kernels.cu`

---

## **69.4 Quantization**
Per-channel INT8 quantization compresses expert weights by approximately 4x, reducing both NVMe transfer time and GPU memory footprint with minimal accuracy loss.

### **69.4.1 Per-Channel Quantization**
Each channel (row) gets its own scale factor computed as `absmax / 127`. This preserves the dynamic range of each output channel independently.

```cpp
// src/kernels/quantize_kernels.cu
quantize_fp32_to_int8(d_quantized, d_scales, d_weights,
                      num_channels, channel_size, stream);
```

**Key Points**:
- Two-pass approach: first finds per-channel absmax, then quantizes
- Values clamped to [-127, 127] range
- Scale factors stored alongside quantized data for dequantization

**Source**: `src/kernels/quantize_kernels.cu`

### **69.4.2 Dequantization**
Reconstruction multiplies each INT8 value by its channel's scale factor.

```cpp
dequantize_int8_to_fp32(d_weights, d_quantized, d_scales,
                        num_channels, channel_size, stream);
```

**Key Points**:
- Roundtrip error bounded by `scale / 127` per element
- Zero values preserved exactly
- Suitable for inference; not recommended for training gradients

---

## **69.5 C API**
A stable C interface hides all C++ and CUDA implementation details behind an opaque handle, making the system accessible from Python, Rust, or other FFI-capable languages.

### **69.5.1 Model Lifecycle**

```cpp
// src/common/llm_api.h
LLMModel model = llm_create_model("config.txt");
int vocab = llm_get_vocab_size(model);
int max_len = llm_get_max_seq_len(model);
long long params = llm_get_num_parameters(model);
llm_destroy_model(model);
```

**Key Points**:
- Config file specifies vocab_size, d_model, num_layers, num_experts
- Defaults applied when config keys are missing
- NULL-safe destroy function

**Source**: `src/common/llm_api.h`, `src/host/c_api.cpp`

### **69.5.2 Autoregressive Generation**

```cpp
int input_ids[] = {1, 42, 100, 256, 500};
int output_ids[50];
int generated = llm_generate(model, input_ids, 5, output_ids, 50);
```

**Key Points**:
- Returns number of tokens generated, or -1 on error
- Stops at EOS token or max_output_len
- All invalid parameter combinations return -1

---

## **69.6 Examples**
Two example programs demonstrate end-to-end usage of the C API.

### **69.6.1 Text Generation**
The `text_generation.cpp` example creates a model, feeds in a prompt as token IDs, generates output tokens, and prints the results.

```bash
./69_MoE_NVMe_Complete_System_text_gen model_config.txt
```

**Source**: `examples/text_generation.cpp`

### **69.6.2 Question Answering**
The `question_answering.cpp` example wraps a user question in a QA prompt template before generating a response.

```bash
./69_MoE_NVMe_Complete_System_qa model_config.txt "What is MoE?"
```

**Source**: `examples/question_answering.cpp`

---

## Build & Run

```bash
# From the repository root build directory
cmake -G Ninja ..
ninja 69_MoE_NVMe_Complete_System_lib
ninja 69_MoE_NVMe_Complete_System_test
ninja 69_MoE_NVMe_Complete_System_text_gen
ninja 69_MoE_NVMe_Complete_System_qa

# Run tests
./69_MoE_NVMe_Complete_System_test

# Run examples
./69_MoE_NVMe_Complete_System_text_gen model_config.txt
./69_MoE_NVMe_Complete_System_qa model_config.txt "What is MoE?"

# Generate documentation
ninja doxygen_69_MoE_NVMe_Complete_System
```

---

## **69.7 Summary**
This capstone module demonstrates a complete MoE-based LLM inference system with NVMe expert offloading.

- **Key Takeaways**:
  - LRU caching transparently manages expert residency between GPU and NVMe
  - Cosine similarity prefetching hides NVMe load latency by predicting needed experts
  - INT8 quantization provides 4x compression with bounded roundtrip error
  - Double-buffered pipelines overlap NVMe I/O with GPU computation
  - A stable C API decouples the inference engine from client language

- **Performance Metrics**:

  | Metric | Value |
  |--------|-------|
  | Cache hit latency | <1 us |
  | NVMe expert load (4 MB, PCIe 4.0) | ~100 us |
  | INT8 compression ratio | ~4x |
  | Pipeline overhead per swap | ~1 us |

- **Common Errors**:

  | Error | Cause | Solution |
  |-------|-------|----------|
  | `llm_create_model` returns NULL | NULL config path | Provide valid path |
  | `llm_generate` returns -1 | Invalid parameters (NULL pointers, zero lengths) | Validate inputs |
  | Low cache hit rate | `max_cached_experts` too small | Increase cache size or reduce active experts |
  | High quantization error | Outlier weights in some channels | Use mixed-precision or clip outliers |

- **Next Steps**:
  - Integrate with Module 50 GPUDirect Storage for zero-copy NVMe-to-GPU expert loading
  - Add multi-GPU support for expert parallelism across devices
  - Implement speculative decoding for faster autoregressive generation

- **References**:
  - [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) -- Base reference
  - [DeepSeek MoE](https://arxiv.org/abs/2401.06066) -- MoE architecture
  - [GPUDirect Storage](https://developer.nvidia.com/gpudirect-storage) -- Direct NVMe-GPU transfers
  - [GPTQ Quantization](https://arxiv.org/abs/2210.17323) -- Weight quantization methods
