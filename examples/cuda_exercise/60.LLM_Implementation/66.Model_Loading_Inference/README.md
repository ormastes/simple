# Part 66: Model Loading and Inference

**Goal**: Implement model weight persistence (binary checkpoints and HuggingFace SafeTensors), KV cache for efficient autoregressive decoding, and beam search for high-quality text generation.

## Project Structure

```
66.Model_Loading_Inference/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── checkpoint.h           # Binary checkpoint format
│   │   ├── safetensors.h          # HuggingFace SafeTensors parser
│   │   └── inference_engine.h     # KV cache, beam search, generation
│   ├── host/
│   │   ├── checkpoint.cpp         # Checkpoint save/load with fwrite/fread
│   │   ├── huggingface_loader.cpp # SafeTensors JSON parsing and tensor loading
│   │   └── beam_search.cpp        # Beam search, InferenceEngine, KV cache helpers
│   └── kernels/
│       └── kv_cache_kernels.cu    # GPU kernels for cache append and rotate
└── test/
    ├── CMakeLists.txt
    └── unit/
        ├── host/
        │   ├── test_checkpoint.cpp    # Checkpoint roundtrip tests
        │   └── test_beam_search.cpp   # Beam search and KV cache tests
        └── kernels/
            └── test_kv_cache.cu       # GPU cache append/rotate tests
```

## Quick Navigation

- [66.1 Binary Checkpoint Format](#661-binary-checkpoint-format)
- [66.2 SafeTensors Loading](#662-safetensors-loading)
- [66.3 KV Cache Management](#663-kv-cache-management)
- [66.4 Beam Search Decoding](#664-beam-search-decoding)
- [66.5 Summary](#665-summary)
- [Build & Run](#build--run)

---

## **66.1 Binary Checkpoint Format**

The binary checkpoint format provides fast save/load for model weights during training and evaluation. It uses a fixed header with magic number validation followed by contiguous tensor data.

### **66.1.1 File Layout**

The checkpoint format stores metadata and data sequentially:

```
[4B magic "LLMC"][4B version][4B num_tensors][8B total_bytes]
[tensor metadata: name_len, name, ndims, shape, offset, num_elements] x N
[contiguous float data]
```

### **66.1.2 Save/Load API**

```cpp
// checkpoint.h - Binary checkpoint interface
bool save_checkpoint(filepath, d_params, tensors);  // Device -> file
bool load_checkpoint(filepath, d_params, tensors);   // File -> device
int64_t get_checkpoint_param_count(filepath);         // Header-only query
```

**Key Points**:
- Magic number `0x4C4C4D43` ("LLMC") validates format
- Header-only queries avoid loading gigabytes of weight data
- Device-to-host copy is done internally by the save/load functions

**Source**: `src/common/checkpoint.h`, `src/host/checkpoint.cpp`

---

## **66.2 SafeTensors Loading**

SafeTensors is HuggingFace's standard format for distributing model weights. This module parses the format to enable loading pretrained models directly from HuggingFace repositories.

### **66.2.1 Format Structure**

A SafeTensors file consists of:
1. **8-byte header size** (little-endian uint64)
2. **JSON metadata** describing tensor names, dtypes, shapes, and byte offsets
3. **Raw tensor data** in the order described by the metadata

### **66.2.2 Implementation**

```cpp
// safetensors.h - HuggingFace format parser
SafeTensorsHeader header;
parse_safetensors("model.safetensors", header);

// Load a specific tensor to GPU (handles F16/BF16 -> F32 conversion)
load_safetensor_data("model.safetensors", header, "model.embed.weight", d_output);
```

**Key Points**:
- Minimal hand-rolled JSON parser (no external dependencies)
- Automatic dtype conversion: F16 and BF16 are upcast to F32
- Memory-mapped file access available via `mmap_safetensors()` for zero-copy loading

**Source**: `src/common/safetensors.h`, `src/host/huggingface_loader.cpp`

---

## **66.3 KV Cache Management**

The KV cache stores previously computed key and value projections during autoregressive generation, avoiding redundant computation for tokens that have already been processed.

### **66.3.1 Cache Structure**

The cache is organized as contiguous memory per layer:

```
KVCache:
  d_key_cache   [num_layers, max_seq_len, num_heads * head_dim]
  d_value_cache [num_layers, max_seq_len, num_heads * head_dim]
  current_len   (number of positions currently cached)
```

### **66.3.2 GPU Kernels**

Two CUDA kernels manage the cache:

```cpp
// kv_cache_kernels.cu
// Append: write new entries at current_len
__global__ void kv_cache_append_kernel(cache, new_data, current_len, num_new, d, max_len);

// Rotate: shift left for sliding window attention
__global__ void kv_cache_rotate_kernel(cache, shift, current_len, d, max_len);
```

**Key Points**:
- Append writes new tokens without touching existing cache entries
- Rotate shifts all entries left by `shift` positions (O(remaining * d) work)
- Position counter is updated only after the last layer to avoid race conditions

**Source**: `src/kernels/kv_cache_kernels.cu`, `src/common/inference_engine.h`

---

## **66.4 Beam Search Decoding**

Beam search explores multiple candidate sequences simultaneously, selecting the highest-scoring complete sequences at the end. This produces higher-quality output than greedy decoding.

### **66.4.1 Algorithm**

At each step:
1. Expand each beam with the top-k vocabulary tokens
2. Score each expanded candidate by cumulative log-probability
3. Keep only the top `beam_size` candidates
4. Stop when all beams are finished or max length is reached

### **66.4.2 Length Normalization**

Raw cumulative log-probabilities favor shorter sequences. Length normalization (Wu et al., 2016) compensates:

```
normalized_score = raw_score / ((5 + length)^alpha / (5 + 1)^alpha)
```

### **66.4.3 InferenceEngine**

```cpp
// inference_engine.h - Complete inference pipeline
InferenceEngine engine(d_params, num_layers, d_model, num_heads, vocab_size, max_seq_len);
engine.allocate_kv_cache();
auto result = engine.beam_search(prompt, beam_size=4, max_length=100, eos_token=50256);
```

**Key Points**:
- Supports greedy, top-k, and beam search decoding strategies
- KV cache is reusable across multiple generation calls (reset between sequences)
- Beam pruning keeps memory bounded regardless of sequence length

**Source**: `src/host/beam_search.cpp`, `src/common/inference_engine.h`

---

## **66.5 Summary**

- **Key Takeaways**:
  - Binary checkpoints provide fast I/O with magic-number validation
  - SafeTensors parser enables direct loading from HuggingFace models
  - KV cache avoids O(n^2) recomputation during autoregressive generation
  - Beam search with length normalization improves generation quality

- **Common Errors**:

| Error | Cause | Solution |
|-------|-------|----------|
| Invalid checkpoint magic | Wrong file or corrupted | Verify file path and format |
| SafeTensors JSON parse failure | Malformed header | Check file integrity, ensure complete download |
| KV cache overflow | Sequence exceeds max_seq_len | Use sliding window rotation or increase max_seq_len |
| Beam search OOM | Large beam_size * vocab_size | Reduce beam_size or use top-k pre-filtering |

- **Next Steps**: [67.DeepSeek_R1_Adaptation](../67.DeepSeek_R1_Adaptation/README.md) - Adapt the architecture for DeepSeek R1 with GQA, RoPE, and SwiGLU

- **References**:
  - [SafeTensors Format](https://huggingface.co/docs/safetensors)
  - [Google's Neural Machine Translation System (Wu et al., 2016)](https://arxiv.org/abs/1609.08144) - Beam search with length normalization
  - [Efficient Transformers: A Survey](https://arxiv.org/abs/2009.06732) - KV cache strategies
  - [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Chapters 4-5

---

## Build & Run

```bash
# Build
cmake -B build -G Ninja
ninja -C build 66_Model_Loading_Inference_test

# Run tests
./build/60.LLM_Implementation/66.Model_Loading_Inference/test/66_Model_Loading_Inference_test

# Generate documentation
ninja -C build doxygen_66_Model_Loading_Inference
```
