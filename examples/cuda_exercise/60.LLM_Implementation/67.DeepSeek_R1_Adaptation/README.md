# Part 67: DeepSeek R1 Adaptation

**Goal**: Adapt the base GPT architecture to match DeepSeek R1 by implementing Grouped Query Attention (GQA), Rotary Position Embeddings (RoPE), and SwiGLU feed-forward networks.

## Project Structure

```
67.DeepSeek_R1_Adaptation/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── deepseek_config.h      # Model configuration
│   │   ├── gqa_attention.h        # GQA interface
│   │   ├── rope_embeddings.h      # RoPE interface
│   │   └── swiglu_ffn.h           # SwiGLU FFN interface
│   ├── host/
│   │   └── deepseek_loader.cpp    # Weight management and checkpoint loading
│   └── kernels/
│       ├── gqa_attention.cu       # GQA CUDA kernels
│       ├── rope_fused.cu          # Fused RoPE CUDA kernels
│       └── swiglu_fused.cu        # Fused SwiGLU CUDA kernels
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_gqa_attention.cu
            ├── test_rope_fused.cu
            └── test_swiglu_fused.cu
```

## Quick Navigation

- [67.1 DeepSeek Architecture](#671-deepseek-architecture)
- [67.2 Grouped Query Attention](#672-grouped-query-attention)
- [67.3 Rotary Position Embeddings](#673-rotary-position-embeddings)
- [67.4 SwiGLU Feed-Forward Network](#674-swiglu-feed-forward-network)
- [67.5 Summary](#675-summary)
- [Build & Run](#build--run)

---

## **67.1 DeepSeek Architecture**

DeepSeek R1 extends the standard GPT architecture with three key modifications that improve efficiency and quality. These changes have been widely adopted across modern LLMs including LLaMA 2/3 and Mistral.

### **67.1.1 Configuration**

The `DeepSeekConfig` struct holds all architectural hyperparameters, with the key distinction being separate counts for query heads and KV heads.

```cpp
// common/deepseek_config.h
struct DeepSeekConfig {
    int num_heads;      // Query heads (e.g., 32)
    int num_kv_heads;   // KV heads (e.g., 8, fewer than query heads)
    float rope_theta;   // RoPE base frequency (e.g., 10000.0)
    int num_experts;    // MoE expert count (0 = dense model)
    // ...
};
```

**Key Points**:
- `num_kv_heads < num_heads` enables GQA (group size = num_heads / num_kv_heads)
- `rope_theta` controls the frequency spectrum of position embeddings
- `num_experts > 0` activates MoE layers (implemented in Module 68)

**Source**: `src/common/deepseek_config.h`

---

## **67.2 Grouped Query Attention**

GQA reduces the memory footprint of the KV cache during inference by sharing KV heads among groups of query heads. Instead of maintaining separate K and V projections for each query head, GQA groups query heads and assigns each group a single shared KV head.

### **67.2.1 GQA vs MHA vs MQA**

| Variant | Q Heads | KV Heads | KV Memory | Quality |
|---------|---------|----------|-----------|---------|
| MHA     | H       | H        | 1x        | Best    |
| GQA     | H       | H/G      | 1/G       | Near-MHA |
| MQA     | H       | 1        | 1/H       | Lower   |

GQA is the practical sweet spot: it reduces KV cache by the group factor G while maintaining nearly the same model quality as full MHA.

### **67.2.2 Implementation**

The GQA kernel splits query heads into groups and computes attention with shared KV:

```cpp
// kernels/gqa_attention.cu
// For each query head h, determine which KV head to use:
int kv_head = h / group_size;  // group_size = num_heads / num_kv_heads
// All query heads in the same group attend to the same K, V
```

**Key Points**:
- Query projection: `[d_model, num_heads * head_dim]`
- Key/Value projection: `[d_model, num_kv_heads * head_dim]` (smaller)
- Output projection concatenates all query heads: `[num_heads * head_dim, d_model]`
- Group size must evenly divide num_heads

**Source**: `src/kernels/gqa_attention.cu`, `src/common/gqa_attention.h`

---

## **67.3 Rotary Position Embeddings**

RoPE encodes position information by rotating pairs of dimensions in the Q and K vectors. Unlike learned or sinusoidal positional embeddings that are added to the input, RoPE modifies the attention computation itself to be position-aware.

### **67.3.1 Rotation Formula**

For each dimension pair (2i, 2i+1) at position p:

```
freq_i = 1.0 / (theta^(2i/d))
angle = p * freq_i
x'[2i]   = x[2i]*cos(angle) - x[2i+1]*sin(angle)
x'[2i+1] = x[2i]*sin(angle) + x[2i+1]*cos(angle)
```

This rotation ensures that the dot product between Q at position m and K at position n depends only on (m - n), providing relative position information.

### **67.3.2 NTK-Aware Scaling**

For extending context length beyond the training window, NTK-aware scaling modifies the base theta:

```
theta_ntk = theta * alpha^(head_dim / (head_dim - 2))
```

This preserves the frequency ratios between dimensions while extending the effective context window.

### **67.3.3 Implementation**

The fused kernel applies RoPE in-place to Q and K tensors:

```cpp
// kernels/rope_fused.cu - Fused RoPE application
rope_forward(Q, K, rope_config, batch, seq_len, num_heads, num_kv_heads);
```

**Key Points**:
- In-place rotation preserves vector norms (rotation is unitary)
- Precomputed cos/sin tables available via `rope_precompute_freqs()`
- Supports position offset for KV-cache scenarios

**Source**: `src/kernels/rope_fused.cu`, `src/common/rope_embeddings.h`

---

## **67.4 SwiGLU Feed-Forward Network**

SwiGLU replaces the traditional ReLU-based FFN with a gated linear unit using the SiLU (Swish) activation. This has been shown to improve model quality across multiple architectures.

### **67.4.1 SwiGLU Computation**

```
output = W_down * (SiLU(W_gate * x) * (W_up * x))
```

where `SiLU(x) = x * sigmoid(x)`.

The gate and up projections are computed independently, then combined through element-wise multiplication after SiLU activation on the gate path.

### **67.4.2 Fused Kernel**

The SiLU activation and element-wise multiplication are fused into a single kernel to avoid writing the intermediate gate and up projection results to global memory:

```cpp
// kernels/swiglu_fused.cu - Fused activation kernel
__global__ void swiglu_fused_activation_kernel(
    float* output, const float* gate, const float* up, int total) {
    float g = gate[idx];
    float silu_g = g / (1.0f + expf(-g));  // SiLU(gate)
    output[idx] = silu_g * up[idx];         // Gated output
}
```

**Key Points**:
- Three weight matrices (W_gate, W_up, W_down) instead of two (W1, W2 in standard FFN)
- SiLU provides smooth gradients compared to ReLU
- Fused kernel reduces memory bandwidth by ~2x for the activation step

**Source**: `src/kernels/swiglu_fused.cu`, `src/common/swiglu_ffn.h`

---

## **67.5 Summary**

- **Key Takeaways**:
  - GQA reduces KV cache memory by sharing KV heads among query head groups
  - RoPE provides relative position awareness through dimension-pair rotations
  - SwiGLU improves FFN quality with gated SiLU activation
  - All three components are fused CUDA kernels for efficiency

- **Common Errors**:

| Error | Cause | Solution |
|-------|-------|----------|
| `num_heads % num_kv_heads != 0` | Invalid GQA config | Ensure num_heads is divisible by num_kv_heads |
| Norm not preserved after RoPE | Bug in rotation | Verify both cos and sin are applied correctly |
| NaN in SwiGLU output | Large gate values | Check weight initialization scale |

- **Next Steps**: [68.MoE_Implementation](../68.MoE_Implementation/README.md) - Add Mixture-of-Experts routing on top of these DeepSeek components

- **References**:
  - [DeepSeek R1 Paper](https://arxiv.org/abs/2401.02954)
  - [GQA: Training Generalized Multi-Query Transformer Models](https://arxiv.org/abs/2305.13245)
  - [RoFormer: Enhanced Transformer with Rotary Position Embedding](https://arxiv.org/abs/2104.09864)
  - [GLU Variants Improve Transformer](https://arxiv.org/abs/2002.05202)

---

## Build & Run

```bash
# Build
cmake -B build -G Ninja
ninja -C build 67_DeepSeek_R1_Adaptation_test

# Run tests
./build/60.LLM_Implementation/67.DeepSeek_R1_Adaptation/test/67_DeepSeek_R1_Adaptation_test

# Generate documentation
ninja -C build doxygen_67_DeepSeek_R1_Adaptation
```
