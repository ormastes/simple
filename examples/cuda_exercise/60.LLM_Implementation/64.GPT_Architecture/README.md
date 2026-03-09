# Part 64: GPT Architecture

**Goal**: Implement the complete GPT (Generative Pre-trained Transformer) model by combining embeddings, attention, and transformer blocks into a unified architecture with forward pass, sampling strategies, and autoregressive text generation.

## Project Structure

```
64.GPT_Architecture/
├── CMakeLists.txt
├── README.md
├── doxygen/
│   ├── Doxyfile.in
│   └── mainpage.md
├── src/
│   ├── CMakeLists.txt
│   ├── common/
│   │   ├── gpt_config.h          # GPT configuration presets
│   │   ├── gpt_model.h           # Model weights and forward pass interface
│   │   └── text_generator.h      # Sampling and generation interface
│   └── kernels/
│       ├── gpt_model.cu          # Model allocation and forward pass
│       ├── sampling.cu           # Top-k and top-p sampling kernels
│       └── text_generator.cu     # Autoregressive generation loop
└── test/
    ├── CMakeLists.txt
    └── unit/
        └── kernels/
            ├── test_gpt_model.cu       # Model tests
            ├── test_sampling.cu        # Sampling strategy tests
            └── test_text_generator.cu  # Generation loop tests
```

## Quick Navigation

- [64.1 GPT Configuration](#641-gpt-configuration)
- [64.2 Model Architecture](#642-model-architecture)
- [64.3 Sampling Strategies](#643-sampling-strategies)
- [64.4 Text Generation](#644-text-generation)
- [64.5 Build & Run](#645-build--run)
- [64.6 Summary](#646-summary)

---

## **64.1 GPT Configuration**

GPT model sizes are defined through a configuration struct that captures all architectural hyperparameters, enabling easy switching between model variants from tiny (for testing) to GPT-2 Large (774M parameters).

### **64.1.1 GPTConfig Structure**

The configuration struct holds all the hyperparameters needed to fully define a GPT model architecture.

```cpp
// src/common/gpt_config.h
struct GPTConfig {
    int vocab_size;    // Vocabulary size (50257 for GPT-2)
    int d_model;       // Model/embedding dimension
    int num_heads;     // Number of attention heads
    int num_layers;    // Number of transformer layers
    int d_ff;          // Feed-forward intermediate dimension (typically 4 * d_model)
    int max_seq_len;   // Maximum sequence length
    float dropout;     // Dropout rate
};
```

**Key Points**:
- `d_model` must be divisible by `num_heads` (each head gets `d_model / num_heads` dimensions)
- `d_ff` is typically `4 * d_model` following the original transformer design
- Default constructor initializes to GPT-2 Small configuration

**Source**: `src/common/gpt_config.h`

### **64.1.2 Model Size Presets**

Factory functions provide standard GPT-2 configurations and a tiny variant for testing.

| Preset | d_model | Layers | Heads | d_ff | Parameters |
|--------|---------|--------|-------|------|------------|
| `gpt_tiny()` | 64 | 2 | 4 | 256 | ~150K |
| `gpt2_small()` | 768 | 12 | 12 | 3072 | ~124M |
| `gpt2_medium()` | 1024 | 24 | 16 | 4096 | ~355M |
| `gpt2_large()` | 1280 | 36 | 20 | 5120 | ~774M |

### **64.1.3 Parameter Counting**

The `count_parameters()` function computes the total number of learnable parameters, accounting for weight tying between token embeddings and the LM head.

```cpp
long long params = count_parameters(gpt2_small());
// Returns ~124M (token embeddings + position embeddings + layers + final norm)
```

**Source**: `src/common/gpt_config.h:count_parameters()`

---

## **64.2 Model Architecture**

The GPT model combines all previously implemented components into a complete language model that maps token ID sequences to vocabulary logits.

### **64.2.1 Weight Structure**

The model organizes weights hierarchically: top-level embeddings and final norm, with per-layer transformer block weights.

```cpp
// src/common/gpt_model.h
struct GPTModelWeights {
    float* token_embeddings;         // [vocab_size, d_model]
    float* position_embeddings;      // [max_seq_len, d_model]
    TransformerBlockWeights* layers; // Array of num_layers blocks
    LayerNormWeights final_norm;     // Final layer normalization
};
```

Each `TransformerBlockWeights` contains:
- **AttentionWeights**: Q, K, V, O projection matrices and biases
- **LayerNormWeights**: Pre-attention and pre-FFN normalization parameters
- **FFNWeights**: Two linear layers (W1, b1, W2, b2) for the feed-forward network

**Key Points**:
- Weight tying: the LM head reuses `token_embeddings` transposed, saving `vocab_size * d_model` parameters
- Xavier initialization for weight matrices, zeros for biases, ones/zeros for LayerNorm gamma/beta

**Source**: `src/common/gpt_model.h`

### **64.2.2 Forward Pass**

The forward pass chains together five stages to transform input token IDs into vocabulary logits.

```
input_ids [batch, seq_len]
    |
    v
Token Embedding Lookup
    |
    + Position Embeddings (element-wise add)
    |
    v
Transformer Block x num_layers:
    |-- LayerNorm1
    |-- Multi-Head Causal Attention
    |-- Residual Add
    |-- LayerNorm2
    |-- Feed-Forward Network (GELU activation)
    |-- Residual Add
    |
    v
Final LayerNorm
    |
    v
LM Head (matmul with token_embeddings^T)
    |
    v
logits [batch, seq_len, vocab_size]
```

**Key Points**:
- Pre-norm architecture (LayerNorm before attention and FFN, following GPT-2)
- Causal attention mask prevents attending to future tokens
- GELU activation in the feed-forward network (approximate version)
- Weight tying for the LM head reduces memory usage

**Source**: `src/kernels/gpt_model.cu:GPTModel::forward()`

---

## **64.3 Sampling Strategies**

Sampling strategies control how the next token is selected from the model's output logit distribution, balancing between quality (high-probability tokens) and diversity (exploration).

### **64.3.1 Top-k Sampling**

Top-k sampling restricts the candidate set to the k tokens with the highest logits, then samples from the resulting distribution.

```
logits -> sort descending -> keep top k -> apply temperature -> softmax -> sample
```

```cpp
// Sample from top 50 candidates
gpu_top_k_sampling(d_token, d_logits, vocab_size, /*top_k=*/50, /*temperature=*/0.8f);
```

**Key Points**:
- `k=1` is equivalent to greedy decoding (always picks the argmax)
- Temperature < 1.0 sharpens the distribution (more deterministic)
- Temperature > 1.0 flattens the distribution (more random)
- Implementation uses a single GPU block with shared memory for the partial sort

**Source**: `src/kernels/sampling.cu:gpu_top_k_sampling()`

### **64.3.2 Top-p (Nucleus) Sampling**

Nucleus sampling dynamically adjusts the candidate set size by including tokens until their cumulative probability exceeds a threshold p.

```
logits -> softmax -> sort by probability -> cumulative sum -> keep until cumsum >= p -> re-normalize -> sample
```

```cpp
// Sample from nucleus with 90% cumulative probability
gpu_top_p_sampling(d_token, d_logits, vocab_size, /*top_p=*/0.9f, /*temperature=*/1.0f);
```

**Key Points**:
- Adapts to the distribution shape: uses fewer candidates when the model is confident
- `top_p=1.0` samples from the full distribution (no filtering)
- Can be combined with temperature scaling for additional control
- More robust than top-k when logit distributions vary across positions

**Source**: `src/kernels/sampling.cu:gpu_top_p_sampling()`

---

## **64.4 Text Generation**

The text generation loop combines the model forward pass with sampling to produce token sequences autoregressively.

### **64.4.1 Autoregressive Loop**

Each iteration runs the full model to get logits, samples the next token, and extends the sequence.

```cpp
// src/common/text_generator.h
SamplingConfig config;
config.temperature = 0.8f;
config.top_k = 50;
config.max_new_tokens = 100;

generate(d_output, model, d_prompt, prompt_len, config);
```

**Key Points**:
- The prompt is preserved at the beginning of the output sequence
- Without KV-cache, each step re-computes attention over the full sequence (O(n^2) per step, O(n^3) total)
- Generation stops when `max_new_tokens` is reached or sequence length hits `max_seq_len`
- Top-k is used when `top_k > 0`, otherwise falls back to top-p

**Source**: `src/kernels/text_generator.cu:generate()`

### **64.4.2 SamplingConfig**

The sampling configuration struct controls all aspects of the generation process.

```cpp
struct SamplingConfig {
    float temperature = 1.0f;    // Logit scaling (lower = more deterministic)
    int top_k = 50;              // Top-k candidates (0 = disabled, use top-p)
    float top_p = 0.9f;          // Nucleus probability threshold
    int max_new_tokens = 100;    // Maximum generated tokens
};
```

---

## **64.5 Build & Run**

This module depends on Modules 61 (embeddings), 62 (attention), and 63 (transformer blocks).

### Build

```bash
cd /path/to/build
cmake .. -G Ninja
ninja 64_GPT_Architecture_test
```

### Run Tests

```bash
./60.LLM_Implementation/64.GPT_Architecture/64_GPT_Architecture_test
```

### Generate Documentation

```bash
ninja doxygen_64_GPT_Architecture
```

---

## **64.6 Summary**

- **Key Takeaways**:
  - GPT combines token embeddings, position embeddings, transformer blocks, and a weight-tied LM head into a complete language model
  - Configuration presets allow easy switching between model sizes (tiny for testing, full GPT-2 variants)
  - Top-k and top-p sampling provide control over generation quality vs. diversity tradeoff
  - Autoregressive generation re-runs the full forward pass at each step (KV-cache optimization left for future work)
  - Weight tying between token embeddings and LM head reduces parameter count without loss of quality

- **Parameter Counts**:
  | Config | Parameters | Memory (FP32) |
  |--------|------------|---------------|
  | gpt_tiny | ~150K | ~600 KB |
  | gpt2_small | ~124M | ~496 MB |
  | gpt2_medium | ~355M | ~1.4 GB |
  | gpt2_large | ~774M | ~3.1 GB |

- **Common Errors**:

  | Error | Cause | Solution |
  |-------|-------|----------|
  | CUDA OOM on allocate | Model too large for GPU | Use `gpt_tiny()` for testing |
  | NaN in logits | Numerical overflow in attention | Check sequence length < max_seq_len |
  | All identical outputs | Temperature too low or top_k=1 | Increase temperature or top_k |
  | Slow generation | No KV-cache, O(n^3) total | Future: implement KV-cache in Module 65+ |

- **Next Steps**: [65.Training_Infrastructure](../65.Training_Infrastructure/README.md) - Loss computation, backpropagation, and optimizer integration

- **References**:
  - [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Sebastian Raschka
  - [Language Models are Unsupervised Multitask Learners](https://cdn.openai.com/better-language-models/language_models_are_unsupervised_multitask_learners.pdf) - GPT-2 paper
  - [The Curious Case of Neural Text Degeneration](https://arxiv.org/abs/1904.09751) - Nucleus sampling paper
  - [Attention Is All You Need](https://arxiv.org/abs/1706.03762) - Transformer architecture
