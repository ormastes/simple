# Module 63: Transformer Blocks

## Overview

This module implements the core building blocks of a transformer layer for large language models. It provides Layer Normalization, RMS Normalization, a position-wise Feed-Forward Network (FFN), and a complete pre-norm transformer block with residual connections.

Based on "Attention Is All You Need" (Vaswani et al., 2017) and modern LLM architectures such as GPT-2 and LLaMA.

## Architecture

The module is organized into the following components:

### Normalization (common/, kernels/)
- **LayerNorm**: Standard layer normalization (GPT-2, BERT)
- **RMSNorm**: Root mean square normalization (LLaMA, DeepSeek)

### Feed-Forward Network (common/, kernels/)
- **FFN**: Position-wise feed-forward with GELU activation
- **GELU Kernel**: Approximate GELU using tanh

### Transformer Block (common/, kernels/)
- **TransformerBlock**: Complete pre-norm block with residual connections
- **Vector Add**: Element-wise addition for residual connections

## Key APIs

### Layer Normalization
- @ref llm::layer_norm_forward() - Forward pass
- @ref llm::allocate_layer_norm_weights() - Weight allocation
- @ref llm::layer_norm_kernel() - CUDA kernel

### RMS Normalization
- @ref llm::rms_norm_forward() - Forward pass
- @ref llm::allocate_rms_norm_weights() - Weight allocation
- @ref llm::rms_norm_kernel() - CUDA kernel

### Feed-Forward Network
- @ref llm::ffn_forward() - Forward pass
- @ref llm::allocate_ffn_weights() - Weight allocation
- @ref llm::gelu_kernel() - GELU activation kernel

### Transformer Block
- @ref llm::transformer_block_forward() - Forward pass
- @ref llm::allocate_transformer_block_weights() - Weight allocation

## Testing

Unit tests in `test/unit/kernels/`:
- `test_layer_norm.cu`: Verifies zero mean, unit variance, CPU reference match
- `test_rms_norm.cu`: Verifies CPU reference match, output RMS near 1.0
- `test_feed_forward.cu`: Verifies output shape, non-trivial output, GELU correctness
- `test_transformer_block.cu`: Verifies forward pass, residual connections, both norm variants

## References

- [Attention Is All You Need](https://arxiv.org/abs/1706.03762) - Transformer architecture
- [Layer Normalization](https://arxiv.org/abs/1607.06450) - Ba et al., 2016
- [Root Mean Square Layer Normalization](https://arxiv.org/abs/1910.07467) - Zhang & Sennrich, 2019
- [GELU Activation](https://arxiv.org/abs/1606.08415) - Hendrycks & Gimpel, 2016
- [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Base reference
