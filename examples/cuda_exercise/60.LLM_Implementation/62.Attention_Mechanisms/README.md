# 🎯 Part 62: Attention Mechanisms

**Goal**: Implement scaled dot-product attention, causal (autoregressive) attention, and multi-head attention as the core building blocks of transformer-based language models.

## Project Structure
```
62.Attention_Mechanisms/
├── README.md          - This documentation
├── CMakeLists.txt     - Build configuration
├── src/               - Source implementations
│   ├── common/        - Headers and shared data structures
│   │   ├── self_attention.h
│   │   ├── causal_attention.h
│   │   └── multi_head_attention.h
│   ├── host/          - CPU-side implementations
│   │   └── attention_setup.cpp
│   └── kernels/       - CUDA kernel implementations
│       ├── attention_naive.cu
│       └── multi_head_attention.cu
├── test/              - Test files
│   └── unit/
│       ├── host/
│       │   └── test_attention_setup.cpp
│       └── kernels/
│           ├── test_attention_naive.cu
│           └── test_multi_head_attention.cu
└── doxygen/           - API documentation
    ├── Doxyfile.in
    └── mainpage.md
```

## Quick Navigation
- [62.1 Self-Attention](#621-self-attention)
- [62.2 Causal Attention](#622-causal-attention)
- [62.3 Multi-Head Attention](#623-multi-head-attention)
- [62.4 Build & Run](#624-build--run)
- [62.5 Summary](#625-summary)

---

## **62.1 Self-Attention**

Self-attention is the core mechanism that allows a transformer to weigh the relevance of each token in a sequence relative to every other token. It computes context-aware representations by letting each position "attend" to all other positions.

### **62.1.1 Scaled Dot-Product Attention**

The fundamental attention operation computes a weighted sum of values, where weights are determined by the compatibility between queries and keys.

**Formula**:
```
Attention(Q, K, V) = softmax(QK^T / sqrt(d_k)) * V
```

where:
- **Q** (Query): What information am I looking for? `[batch, seq_len, d_model]`
- **K** (Key): What information do I contain? `[batch, seq_len, d_model]`
- **V** (Value): What information do I provide? `[batch, seq_len, d_model]`
- **d_k**: Dimension per attention head (for scaling)

The scaling factor `1/sqrt(d_k)` prevents dot products from growing too large, which would push softmax into regions with vanishingly small gradients.

### **62.1.2 Implementation**

Source: `src/kernels/attention_naive.cu`

The naive implementation breaks attention into four steps:

```cpp
// Step 1: Compute QK^T scores per head
// scores[i][j] = sum_k Q[i][k] * K[j][k] / sqrt(head_dim)
compute_attention_scores_kernel<<<grid, block>>>(scores, Q_head, K_head, seq_len, head_dim, scale);

// Step 2: Apply softmax row-wise (numerically stable)
softmax_rows_kernel<<<blocks, threads>>>(scores, seq_len);

// Step 3: Multiply attention weights by V
// output[i] = sum_j attn_weights[i][j] * V[j]
attention_value_multiply_kernel<<<grid, block>>>(output, scores, V_head, seq_len, head_dim);
```

**Key Points**:
- Each head processes independently with head_dim = d_model / num_heads
- Softmax uses the max-subtraction trick for numerical stability
- This is a reference implementation; production would use FlashAttention or cuBLAS

**Source**: `src/kernels/attention_naive.cu`, `src/common/self_attention.h`

### **62.1.3 Attention Configuration**

```cpp
// src/common/self_attention.h
struct AttentionConfig {
    int d_model;      // Model dimension (e.g., 768 for GPT-2)
    int num_heads;    // Number of attention heads (e.g., 12)
    int head_dim;     // Dimension per head (d_model / num_heads = 64)
    int max_seq_len;  // Maximum sequence length (e.g., 1024)
    float dropout;    // Dropout rate (0.0 = no dropout)

    AttentionConfig(int d_model, int num_heads, int max_seq_len = 1024, float dropout = 0.0f);
};
```

---

## **62.2 Causal Attention**

Causal attention restricts the attention pattern so that each token can only attend to previous tokens and itself. This is essential for autoregressive language models (like GPT) where the model generates tokens left-to-right and must not peek at future tokens.

### **62.2.1 Causal Mask**

The causal mask sets attention scores for future positions to negative infinity before softmax, ensuring zero attention weight:

```
Mask matrix (4x4):
     pos 0  pos 1  pos 2  pos 3
pos 0 [  0    -inf   -inf   -inf ]   <- Token 0 sees only itself
pos 1 [  0      0    -inf   -inf ]   <- Token 1 sees 0, 1
pos 2 [  0      0      0    -inf ]   <- Token 2 sees 0, 1, 2
pos 3 [  0      0      0      0  ]   <- Token 3 sees all tokens
```

After softmax, the masked positions become exactly zero.

### **62.2.2 Implementation**

Source: `src/kernels/attention_naive.cu`

```cpp
// Apply causal mask: set scores[i][j] = -inf where j > i
__global__ void apply_causal_mask_kernel(float* scores, int seq_len) {
    int row = blockIdx.x * blockDim.x + threadIdx.x;
    int col = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < seq_len && col < seq_len) {
        if (col > row) {
            scores[row * seq_len + col] = -FLT_MAX;
        }
    }
}
```

**Key Points**:
- Uses `-FLT_MAX` instead of `-INFINITY` to avoid NaN in softmax
- Applied between score computation and softmax
- The first token always produces the same output whether causal or not (it only has itself to attend to)

**Source**: `src/kernels/attention_naive.cu`, `src/common/causal_attention.h`

### **62.2.3 Why Causal Masking Matters**

Without causal masking, a language model could "cheat" during training by looking at the answer (future tokens). Causal masking ensures the model learns to predict each token using only the preceding context, which matches how it will be used during inference (token-by-token generation).

---

## **62.3 Multi-Head Attention**

Multi-head attention runs multiple attention operations in parallel, each with different learned projections. This allows the model to jointly attend to information from different representation subspaces at different positions.

### **62.3.1 Architecture**

The multi-head attention layer consists of five steps:

```
Input [batch, seq_len, d_model]
  |
  +---> W_Q projection --> Q [batch, seq_len, d_model]
  +---> W_K projection --> K [batch, seq_len, d_model]
  +---> W_V projection --> V [batch, seq_len, d_model]
  |
  |   Split into num_heads heads:
  |     Head 0: Q[:,:,0:64], K[:,:,0:64], V[:,:,0:64]
  |     Head 1: Q[:,:,64:128], K[:,:,64:128], V[:,:,64:128]
  |     ...
  |
  |   Attention per head:
  |     attn_h = softmax(Q_h * K_h^T / sqrt(d_k)) * V_h
  |
  |   Concatenate heads:
  |     concat = [attn_0 | attn_1 | ... | attn_H]
  |
  +---> W_O projection --> Output [batch, seq_len, d_model]
```

### **62.3.2 Weight Matrices**

```cpp
// src/common/self_attention.h
struct AttentionWeights {
    float* W_Q;  // Query projection  [d_model, d_model]
    float* W_K;  // Key projection    [d_model, d_model]
    float* W_V;  // Value projection  [d_model, d_model]
    float* W_O;  // Output projection [d_model, d_model]
    float* b_Q;  // Query bias  [d_model]
    float* b_K;  // Key bias    [d_model]
    float* b_V;  // Value bias  [d_model]
    float* b_O;  // Output bias [d_model]
};
```

### **62.3.3 Implementation**

Source: `src/kernels/multi_head_attention.cu`

```cpp
void multi_head_attention_forward(float* output, const float* input,
                                 const AttentionWeights& weights,
                                 const AttentionConfig& config,
                                 int batch_size, int seq_len,
                                 bool causal, cudaStream_t stream) {
    // Step 1: Linear projections
    // Q = input * W_Q^T + b_Q
    linear_forward(d_Q, input, weights.W_Q, weights.b_Q, ...);
    linear_forward(d_K, input, weights.W_K, weights.b_K, ...);
    linear_forward(d_V, input, weights.W_V, weights.b_V, ...);

    // Step 2-3: Attention (splits into heads internally)
    if (causal)
        causal_attention_forward(d_attn_out, d_Q, d_K, d_V, config, ...);
    else
        self_attention_forward(d_attn_out, d_Q, d_K, d_V, config, ...);

    // Step 4: Output projection
    linear_forward(output, d_attn_out, weights.W_O, weights.b_O, ...);
}
```

**Key Points**:
- Each head learns different attention patterns (syntax, semantics, coreference, etc.)
- Weight matrices W_Q, W_K, W_V, W_O are all [d_model, d_model] (combined across heads)
- Linear projections use naive matrix multiply (production would use cuBLAS)

**Source**: `src/kernels/multi_head_attention.cu`, `src/common/multi_head_attention.h`

### **62.3.4 Weight Management**

```cpp
#include "common/multi_head_attention.h"

using namespace llm;

AttentionConfig config(768, 12);  // d_model=768, 12 heads

// Allocate weights on GPU
AttentionWeights weights = allocate_attention_weights(config);

// Initialize with Xavier/Glorot scheme
initialize_attention_weights(weights, config, /*seed=*/42);

// ... use weights in multi_head_attention_forward() ...

// Free GPU memory
free_attention_weights(weights);
```

---

## **62.4 Build & Run**

### **Build Instructions**

```bash
# From project root
cd build

# Configure (if not already done)
cmake -B . -G Ninja ..

# Build module 62
ninja 62_Attention_Mechanisms_test

# Run tests
ctest --test-dir . -R 62_Attention_Mechanisms --output-on-failure
```

### **Run Individual Tests**

```bash
# Test attention setup (allocation, initialization)
./62_Attention_Mechanisms_test --gtest_filter="AttentionSetupTest*"

# Test naive attention kernels
./62_Attention_Mechanisms_test --gtest_filter="AttentionNaiveTest*"

# Test multi-head attention
./62_Attention_Mechanisms_test --gtest_filter="MultiHeadAttentionTest*"
```

### **Profiling**

```bash
# Nsight Systems profiling
ninja run_nsys_62_Attention_Mechanisms_test

# Nsight Compute profiling
ninja run_ncu_62_Attention_Mechanisms_test
```

### **Generate Documentation**

```bash
ninja doxygen_62_Attention_Mechanisms
```

---

## **62.5 Summary**

### **Key Takeaways**

1. **Self-Attention**: Computes context-aware representations by letting each token attend to all others. The scaling factor `1/sqrt(d_k)` is critical for stable softmax gradients.

2. **Causal Attention**: Restricts attention to prevent future information leakage. Essential for autoregressive (left-to-right) language generation.

3. **Multi-Head Attention**: Runs parallel attention with different learned projections. Each head captures different linguistic relationships (syntax, semantics, coreference).

4. **Complexity**: Self-attention has O(n^2) complexity in sequence length, which becomes the bottleneck for long sequences. This motivates optimizations like FlashAttention (Module 62+).

5. **Weight Management**: Xavier initialization prevents vanishing/exploding gradients. Zero-initialized biases provide a neutral starting point.

### **Performance Characteristics**

| Component | Input Size | Complexity | Notes |
|-----------|-----------|-----------|-------|
| Score Computation (QK^T) | [B, S, D] | O(B * H * S^2 * d_k) | Memory-bound for small S |
| Softmax | [B, H, S, S] | O(B * H * S^2) | 3 passes over data |
| Value Multiply | [B, H, S, S] x [B, H, S, d_k] | O(B * H * S^2 * d_k) | Compute-bound |
| Linear Projection | [B*S, D] x [D, D] | O(B * S * D^2) | cuBLAS-optimizable |

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| NaN in output | Softmax overflow | Use max-subtraction trick (already implemented) |
| d_model not divisible by num_heads | Invalid config | Ensure d_model % num_heads == 0 |
| CUDA out of memory | Large seq_len^2 scores | Reduce batch size or seq_len |
| Wrong output shape | Mismatched head scatter | Verify head_dim * num_heads == d_model |

### **Next Steps**

- Continue to [Part 63: Transformer Blocks](../63.Transformer_Blocks/README.md) to compose attention with feed-forward networks and layer normalization
- Optimize attention with FlashAttention-style tiling for O(1) memory
- Experiment with different numbers of heads and head dimensions
- Add KV-cache for efficient autoregressive inference

### **References**

- [Attention Is All You Need](https://arxiv.org/abs/1706.03762) - Vaswani et al., 2017
- [LLMs from Scratch - Chapter 3](https://github.com/rasbt/LLMs-from-scratch) - Base reference
- [The Illustrated Transformer](https://jalammar.github.io/illustrated-transformer/) - Visual guide
- [FlashAttention](https://arxiv.org/abs/2205.14135) - IO-Aware Exact Attention
- [GPT-2 Paper](https://cdn.openai.com/better-language-models/language_models_are_unsupervised_multitask_learners.pdf) - OpenAI, 2019
