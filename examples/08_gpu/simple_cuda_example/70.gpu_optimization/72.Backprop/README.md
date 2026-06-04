# Backpropagation Kernels

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** GPU-accelerated backpropagation with gradient computation and atomics

## Simple Approach

Simple implements backpropagation using GPU kernels for gradient computation. Atomic
operations are used for safe gradient accumulation across threads. The implementation
covers the core operations needed for training neural networks.

Key features:
- **Atomic gradient accumulation:** `atomic_add` for thread-safe weight updates
- **Per-layer gradient kernels:** Separate kernels for linear, activation, and loss
- **Chain rule composition:** Gradients flow backward through layer stack
- **Error handling:** `Result<T, GpuError>` for all GPU operations

## Concepts Covered

- Gradient computation for linear layers
- Gradient of activation functions (ReLU, GELU)
- Cross-entropy loss gradient
- Atomic gradient accumulation
- Weight update with learning rate
- Full backward pass through a simple network

## Files

- `main.spl` - Backpropagation kernels with gradient computation
- `spec.spl` - Tests for gradient correctness
