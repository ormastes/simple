# Module 68: MoE Implementation

## Overview

This module implements the Mixture-of-Experts (MoE) architecture as used in DeepSeek R1. MoE replaces the dense feed-forward network in select transformer layers with a collection of expert networks, where each token is routed to only a subset of experts. This allows the model to scale parameters without proportionally increasing computation.

## Architecture

### Router (common/, kernels/)
- **RouterConfig**: Gating network parameters (num_experts, top_k, capacity)
- **topk_route()**: Softmax gating + top-k expert selection
- **RouterOutput**: Expert indices, weights, and gate logits per token

### Expert Dispatch (kernels/)
- **expert_dispatch_kernel**: Scatter tokens to assigned expert buffers
- **expert_forward()**: SwiGLU FFN forward pass for a single expert
- **ExpertWeights**: Per-expert weight matrices (W_gate, W_up, W_down)

### Expert Combine (kernels/)
- **expert_combine_simple_kernel**: Weighted gather of expert outputs
- **moe_layer_forward()**: Complete router + dispatch + forward + combine pipeline

### Load Balance Loss (kernels/)
- **compute_expert_stats_kernel**: Per-expert selection fraction and mean probability
- **load_balance_loss_kernel**: Importance-weighted auxiliary loss

### MoE Transformer (common/)
- **MoETransformerConfig**: Identifies which layers use MoE vs dense FFN
- **is_moe_layer()**: Check if a given layer index uses MoE

## Key APIs

- @ref llm::topk_route() - Top-k expert routing with softmax gating
- @ref llm::expert_forward() - Single expert SwiGLU forward pass
- @ref llm::moe_layer_forward() - Complete MoE layer pipeline
- @ref llm::is_moe_layer() - Check MoE vs dense layer type

## References

- [DeepSeek R1 Paper](https://arxiv.org/abs/2401.02954) - MoE architecture
- [Switch Transformers (Fedus et al., 2022)](https://arxiv.org/abs/2101.03961) - Load balancing loss
- [GShard (Lepikhin et al., 2021)](https://arxiv.org/abs/2006.16668) - Expert capacity and routing
