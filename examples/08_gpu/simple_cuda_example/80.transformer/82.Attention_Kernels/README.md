# Multi-Head Attention Kernels

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** Production multi-head attention with atomics and shared memory

## Simple Approach

This exercise implements production-quality multi-head attention kernels that combine
shared memory tiling, atomic operations for gradient accumulation, and batched
execution for training workloads. Each attention head runs as a separate GPU
workgroup with shared memory for Q/K/V tiles.

Key features:
- **Batched multi-head:** Process multiple heads and batch items in parallel
- **Shared memory tiles:** Efficient Q/K/V access patterns
- **Atomic accumulation:** Thread-safe output and gradient gathering
- **Fused operations:** Combined QKV projection + attention + output projection

## Concepts Covered

- Batched multi-head attention dispatch
- QKV projection fused kernel
- Per-head shared memory attention
- Atomic output accumulation
- Causal masking per head
- Output projection and concatenation

## Files

- `main.spl` - Multi-head attention kernels with shared memory and atomics
- `spec.spl` - Tests for batched multi-head attention
