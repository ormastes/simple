# Optimized Attention

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** FlashAttention-style optimized attention with tiling and shared memory

## Simple Approach

This exercise implements optimized attention using shared memory tiling and
flash-attention style chunking. Instead of materializing the full attention matrix
(O(n^2) memory), it computes attention in tiles, keeping intermediate results in
shared memory.

Key optimizations:
- **Tiled computation:** Process attention in blocks to fit in shared memory
- **Online softmax:** Compute softmax incrementally without storing full attention matrix
- **Shared memory:** `@shared` arrays for Q, K, V tiles
- **Fused kernel:** Single kernel for scores + softmax + value multiply

## Concepts Covered

- Flash-attention tiling strategy
- Online softmax (log-sum-exp trick)
- Shared memory tile loading
- Memory-efficient attention (O(n) instead of O(n^2))
- Causal masking within tiles

## Files

- `main.spl` - Flash-attention style optimized attention kernel
- `spec.spl` - Tests comparing optimized vs naive attention
