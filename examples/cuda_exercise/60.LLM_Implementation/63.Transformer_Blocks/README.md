# Part 63: Transformer Blocks

**Goal**: Implement the core building blocks of a transformer layer -- Layer Normalization, RMS Normalization, Feed-Forward Networks, and complete pre-norm transformer blocks with residual connections -- as CUDA kernels for LLM inference.

## Project Structure
```
63.Transformer_Blocks/
├── README.md          - This documentation
├── CMakeLists.txt     - Build configuration
├── src/               - Source implementations
│   ├── common/        - Headers and shared data structures
│   │   ├── layer_norm.h
│   │   ├── rms_norm.h
│   │   ├── feed_forward.h
│   │   └── transformer_block.h
│   └── kernels/       - CUDA kernel implementations
│       ├── layer_norm.cu
│       ├── rms_norm.cu
│       ├── feed_forward.cu
│       └── transformer_block.cu
├── test/              - Test files
│   └── unit/
│       └── kernels/
│           ├── test_layer_norm.cu
│           ├── test_rms_norm.cu
│           ├── test_feed_forward.cu
│           └── test_transformer_block.cu
└── doxygen/           - API documentation
    ├── Doxyfile.in
    └── mainpage.md
```

## Quick Navigation
- [63.1 Layer Normalization](#631-layer-normalization)
- [63.2 RMS Normalization](#632-rms-normalization)
- [63.3 Feed-Forward Network](#633-feed-forward-network)
- [63.4 Transformer Block](#634-transformer-block)
- [63.5 Build & Run](#635-build--run)
- [63.6 Summary](#636-summary)

---

## **63.1 Layer Normalization**

Layer Normalization normalizes each sample independently across the feature dimension, computing the mean and variance per row. This is the standard normalization used in GPT-2 and BERT-family models.

### **63.1.1 LayerNorm Formula**

LayerNorm computes per-row statistics and applies a learned affine transformation:

```
output = gamma * (input - mean) / sqrt(variance + eps) + beta
```

Where `mean` and `variance` are computed across the hidden dimension for each row independently. The learnable parameters `gamma` (scale) and `beta` (shift) allow the network to undo the normalization if needed.

### **63.1.2 CUDA Implementation**

Source: `src/kernels/layer_norm.cu`

The kernel uses one thread block per row with shared memory reductions:

```cpp
// src/kernels/layer_norm.cu - LayerNorm kernel (simplified)
__global__ void layer_norm_kernel(float* output, const float* input,
                                  const float* gamma, const float* beta,
                                  int hidden_dim, float eps) {
    int row = blockIdx.x;
    // Step 1: Shared memory reduction for mean
    // Step 2: Shared memory reduction for variance
    // Step 3: Normalize: (x - mean) / sqrt(var + eps) * gamma + beta
}
```

**Key Points**:
- One block per row ensures each row is normalized independently
- Two-pass algorithm: first pass computes mean, second computes variance
- Shared memory reductions for efficient parallel summation
- Block size rounded to next power of 2 for clean reduction

**Source**: `src/kernels/layer_norm.cu`, `src/common/layer_norm.h`

---

## **63.2 RMS Normalization**

RMS Normalization is a simplified variant of LayerNorm that omits the mean-centering step. It is used in modern architectures like LLaMA and DeepSeek, offering similar quality with reduced computation.

### **63.2.1 RMSNorm Formula**

RMSNorm normalizes by the root mean square of the input:

```
output = weight * input * rsqrt(mean(input^2) + eps)
```

Compared to LayerNorm, RMSNorm:
- Does not subtract the mean (no centering)
- Has no beta (shift) parameter
- Requires only one reduction pass (sum of squares) instead of two

### **63.2.2 CUDA Implementation**

Source: `src/kernels/rms_norm.cu`

```cpp
// src/kernels/rms_norm.cu - RMSNorm kernel (simplified)
__global__ void rms_norm_kernel(float* output, const float* input,
                                const float* weight,
                                int hidden_dim, float eps) {
    int row = blockIdx.x;
    // Step 1: Shared memory reduction for sum of squares
    // Step 2: Compute rsqrt(mean_sq + eps)
    // Step 3: Normalize: weight * input * rms_inv
}
```

**Key Points**:
- Single reduction pass (sum of squares) makes it faster than LayerNorm
- No mean subtraction -- simpler kernel with fewer memory accesses
- `rsqrtf()` used for fused reciprocal square root
- Preferred in LLaMA/DeepSeek architectures

**Source**: `src/kernels/rms_norm.cu`, `src/common/rms_norm.h`

---

## **63.3 Feed-Forward Network**

The Feed-Forward Network (FFN) is a position-wise two-layer MLP applied independently to each token. It expands the representation to a higher dimension, applies a nonlinearity, then projects back down.

### **63.3.1 FFN Architecture**

The FFN computes:

```
hidden = GELU(input * W1 + b1)    // Up projection: d_model -> d_ff
output = hidden * W2 + b2          // Down projection: d_ff -> d_model
```

The intermediate dimension `d_ff` is typically 4x the model dimension. The GELU activation provides smooth, non-monotonic gating.

### **63.3.2 GELU Activation**

GELU (Gaussian Error Linear Unit) is the standard activation in transformers:

```
GELU(x) = 0.5 * x * (1 + tanh(sqrt(2/pi) * (x + 0.044715 * x^3)))
```

Properties:
- Smooth approximation of ReLU
- Non-zero gradient for negative inputs (unlike ReLU)
- Empirically better than ReLU for language modeling

### **63.3.3 Implementation**

Source: `src/kernels/feed_forward.cu`

The implementation uses three kernels:
1. `matmul_bias_kernel`: Naive matrix multiplication with bias addition
2. `gelu_kernel`: In-place GELU activation using the tanh approximation
3. `matmul_bias_kernel`: Second linear projection back to model dimension

```cpp
// src/kernels/feed_forward.cu - FFN forward (simplified)
void ffn_forward(float* output, const float* input,
                const FFNWeights& weights, const FFNConfig& config,
                int batch_size, int seq_len, cudaStream_t stream) {
    // Step 1: hidden = input * W1 + b1
    // Step 2: hidden = GELU(hidden)
    // Step 3: output = hidden * W2 + b2
}
```

**Key Points**:
- Naive matmul for clarity; production code would use cuBLAS
- GELU uses the tanh approximation (matching PyTorch/HuggingFace)
- Intermediate buffer allocated/freed per call
- Xavier initialization for weight matrices

**Source**: `src/kernels/feed_forward.cu`, `src/common/feed_forward.h`

---

## **63.4 Transformer Block**

The complete transformer block combines multi-head self-attention and feed-forward network with pre-norm residual connections. This is the fundamental repeating unit in transformer-based LLMs.

### **63.4.1 Pre-Norm Architecture**

Modern transformers use pre-normalization (norm before sublayer) rather than post-normalization:

```
residual1 = input + Attention(Norm(input))
output    = residual1 + FFN(Norm(residual1))
```

Pre-norm is preferred because it stabilizes training and allows deeper stacking of layers without gradient issues.

### **63.4.2 Residual Connections**

Residual (skip) connections add the input directly to the sublayer output. This enables:
- Gradient flow through deep networks
- Identity mapping as a baseline (sublayer learns the residual)
- Stable training of models with hundreds of layers

### **63.4.3 Implementation**

Source: `src/kernels/transformer_block.cu`

```cpp
// src/kernels/transformer_block.cu - Transformer block forward (simplified)
void transformer_block_forward(float* output, const float* input, ...) {
    // Step 1: norm_out = Norm(input)
    // Step 2: attn_out = MultiHeadAttention(norm_out)
    // Step 3: residual1 = input + attn_out
    // Step 4: norm_out2 = Norm(residual1)
    // Step 5: ffn_out = FFN(norm_out2)
    // Step 6: output = residual1 + ffn_out
}
```

**Key Points**:
- Supports both LayerNorm (GPT-2) and RMSNorm (LLaMA) via config flag
- Residual connections implemented with simple vector addition kernel
- Attention is currently a placeholder (will use module 62 once available)
- Temporary buffers allocated for intermediate results

**Source**: `src/kernels/transformer_block.cu`, `src/common/transformer_block.h`

### **63.4.4 Normalization Comparison**

| Feature | LayerNorm | RMSNorm |
|---------|-----------|---------|
| Mean subtraction | Yes | No |
| Learnable shift (beta) | Yes | No |
| Reduction passes | 2 (mean + variance) | 1 (sum of squares) |
| Used in | GPT-2, BERT | LLaMA, DeepSeek |
| Relative speed | Baseline | ~1.3x faster |

---

## **63.5 Build & Run**

### **Build Instructions**

```bash
# From project root
cd 60.LLM_Implementation/63.Transformer_Blocks

# Configure build
cmake -B build -G Ninja

# Build all targets
ninja -C build

# Run tests
cd build && ctest --output-on-failure
```

### **Run Individual Tests**

```bash
# Test layer normalization
./build/63_Transformer_Blocks_test --gtest_filter="LayerNorm*"

# Test RMS normalization
./build/63_Transformer_Blocks_test --gtest_filter="RMSNorm*"

# Test feed-forward network
./build/63_Transformer_Blocks_test --gtest_filter="FeedForward*"

# Test transformer block
./build/63_Transformer_Blocks_test --gtest_filter="TransformerBlock*"
```

### **Profiling Targets**

```bash
# Nsight Systems profiling
ninja run_nsys_63_Transformer_Blocks_test

# Nsight Compute profiling
ninja run_ncu_63_Transformer_Blocks_test
```

### **Generate Documentation**

```bash
ninja doxygen_63_Transformer_Blocks
```

---

## **63.6 Summary**

### **Key Takeaways**

1. **Layer Normalization** normalizes each row to zero mean and unit variance, with learnable scale/shift parameters; it is the standard for GPT-2 and BERT.
2. **RMS Normalization** simplifies LayerNorm by removing mean-centering, providing faster computation with comparable quality; preferred in LLaMA and DeepSeek.
3. **Feed-Forward Network** applies a two-layer MLP with GELU activation to each token independently, expanding to 4x model dimension and projecting back.
4. **Transformer Block** combines attention and FFN with pre-norm residual connections, forming the fundamental repeating unit of transformer LLMs.
5. **Residual connections** are critical for training deep networks, allowing gradients to flow and enabling the sublayers to learn incremental transformations.

### **Performance Metrics**

| Component | Input Size | Expected Performance |
|-----------|-----------|---------------------|
| LayerNorm | [32, 512, 768] | ~0.1 ms |
| RMSNorm | [32, 512, 768] | ~0.07 ms |
| FFN (naive matmul) | [32, 512, 768] | ~5 ms |
| Transformer Block | [32, 512, 768] | ~10 ms |

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| NaN in output | Variance near zero | Increase eps parameter |
| Incorrect norm stats | Block size not power of 2 | Ensure reduction block size is power of 2 |
| Dimension mismatch | d_ff != 4*d_model | Verify FFNConfig dimensions |
| Memory allocation failure | Large batch/seq/model | Reduce batch size or use streaming |

### **Next Steps**

- Continue to [Part 64: GPT Architecture](../64.GPT_Architecture/README.md) to assemble a complete GPT model from these blocks
- Replace naive matmul with cuBLAS for production-level FFN performance
- Integrate module 62 attention mechanisms for full transformer functionality

### **References**

- [Attention Is All You Need](https://arxiv.org/abs/1706.03762) - Transformer architecture (Vaswani et al., 2017)
- [Layer Normalization](https://arxiv.org/abs/1607.06450) - Ba, Kiros, Hinton, 2016
- [Root Mean Square Layer Normalization](https://arxiv.org/abs/1910.07467) - Zhang & Sennrich, 2019
- [Gaussian Error Linear Units](https://arxiv.org/abs/1606.08415) - GELU activation (Hendrycks & Gimpel, 2016)
- [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Sebastian Raschka
