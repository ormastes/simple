# Module 62: Attention Mechanisms

## Overview

This module implements the core attention mechanisms used in transformer-based language models, progressing from basic scaled dot-product attention to full multi-head attention with causal masking.

Based on "LLMs from Scratch" by Sebastian Raschka (Chapter 3) and "Attention Is All You Need" (Vaswani et al., 2017).

## Architecture

The module is organized into the following components:

### Attention Core (common/)
- **AttentionConfig**: Configuration struct for attention hyperparameters (d_model, num_heads, head_dim)
- **AttentionWeights**: Container for QKV projection weight matrices and biases
- **self_attention.h**: Scaled dot-product attention interface
- **causal_attention.h**: Causal (autoregressive) attention with future token masking
- **multi_head_attention.h**: Complete multi-head attention with projections

### Host Setup (host/)
- **attention_setup.cpp**: Weight allocation, Xavier initialization, and cleanup

### GPU Kernels (kernels/)
- **attention_naive.cu**: Reference implementation of self-attention and causal attention
- **multi_head_attention.cu**: Multi-head attention with linear projections

## Key APIs

### Self-Attention
- @ref llm::self_attention_forward() - Scaled dot-product attention (no masking)
- @ref llm::causal_attention_forward() - Causal attention (masks future tokens)

### Multi-Head Attention
- @ref llm::multi_head_attention_forward() - Complete MHA with QKV projections
- @ref llm::allocate_attention_weights() - Allocate weight matrices on device
- @ref llm::free_attention_weights() - Free weight matrices
- @ref llm::initialize_attention_weights() - Xavier/Glorot initialization

## Usage Example

```cpp
#include "common/multi_head_attention.h"

using namespace llm;

// Configure: 768-dim model, 12 heads, max 1024 tokens
AttentionConfig config(768, 12, 1024);

// Allocate and initialize weights
AttentionWeights weights = allocate_attention_weights(config);
initialize_attention_weights(weights, config);

// Input: [batch=2, seq_len=128, d_model=768] on GPU
float* d_input;  // pre-allocated
float* d_output; // pre-allocated

// Forward pass (causal masking for autoregressive generation)
multi_head_attention_forward(d_output, d_input, weights, config,
                            /*batch_size=*/2, /*seq_len=*/128,
                            /*causal=*/true);

// Cleanup
free_attention_weights(weights);
```

## Testing

Unit tests are available in `test/unit/`:
- `test_attention_setup.cpp`: Weight allocation, initialization, config construction
- `test_attention_naive.cu`: Self-attention and causal attention correctness vs CPU reference
- `test_multi_head_attention.cu`: MHA forward shape, determinism, causal vs non-causal

## References

- [Attention Is All You Need](https://arxiv.org/abs/1706.03762) - Original transformer paper
- [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Chapter 3
- [The Illustrated Transformer](https://jalammar.github.io/illustrated-transformer/) - Visual guide
