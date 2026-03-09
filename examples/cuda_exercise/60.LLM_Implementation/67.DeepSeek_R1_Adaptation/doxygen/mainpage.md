# Module 67: DeepSeek R1 Adaptation

## Overview

This module adapts the base GPT architecture from Modules 61-66 to match the DeepSeek R1 model design. It implements the three key architectural differences that distinguish DeepSeek R1 from vanilla GPT: Grouped Query Attention (GQA), Rotary Position Embeddings (RoPE), and SwiGLU feed-forward networks.

## Architecture

### Grouped Query Attention (GQA)
- Reduces KV cache memory by sharing KV heads among multiple query heads
- Configurable head group size (num_heads / num_kv_heads)
- Drop-in replacement for standard multi-head attention

### Rotary Position Embeddings (RoPE)
- Encodes position information through rotation of dimension pairs
- Supports NTK-aware scaling for extended context lengths
- Configurable base frequency (theta parameter)

### SwiGLU Feed-Forward Network
- Replaces ReLU with gated SiLU activation: SiLU(W_gate * x) * (W_up * x)
- Uses three projection matrices instead of two
- Fused kernel for reduced memory traffic

## Key APIs

- @ref llm::gqa_forward() - Grouped Query Attention forward pass
- @ref llm::rope_forward() - Apply RoPE to Q/K tensors
- @ref llm::swiglu_forward() - SwiGLU FFN forward pass
- @ref llm::DeepSeekConfig - Model configuration struct

## References

- [DeepSeek R1 Paper](https://arxiv.org/abs/2401.02954)
- [GQA Paper (Ainslie et al., 2023)](https://arxiv.org/abs/2305.13245)
- [RoFormer (Su et al., 2021)](https://arxiv.org/abs/2104.09864)
- [GLU Variants (Shazeer, 2020)](https://arxiv.org/abs/2002.05202)
