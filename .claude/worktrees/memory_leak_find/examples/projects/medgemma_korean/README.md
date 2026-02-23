# MedGemma Korean - Progressive LoRA Training in Simple

Real GPU training example demonstrating progressive LoRA training to prevent catastrophic forgetting, implemented in the Simple language using libtorch FFI on CUDA.

## Overview

This example trains a neural network model for Korean medical applications using **progressive LoRA stacking** on CUDA GPU. Each training phase adds a new LoRA adapter while freezing previous knowledge.

### Training Phases

```
Phase 0: Plain Text (Korean fluency)
    Base (frozen) + LoRA_0 (trainable)  →  merge LoRA_0 into base
    ↓
Phase 1: Medical Dictionary (terminology)
    [Base + LoRA_0] (frozen) + LoRA_1 (trainable)  →  merge LoRA_1
    ↓
Phase 2: MCQ (medical reasoning)
    [Base + LoRA_0 + LoRA_1] (frozen) + LoRA_2 (trainable)  →  merge LoRA_2
```

**Key Concept**: Each phase merges previous LoRAs into the base model (W = W + B @ A * scale), then adds a new trainable LoRA. This prevents catastrophic forgetting.

---

## Prerequisites

1. **CUDA GPU** with PyTorch/libtorch installed
2. **Build the torch FFI bridge**:
```bash
bash scripts/build/build-torch-ffi.sh
```

This compiles `src/runtime/torch_ffi.cpp` into `build/libspl_torch.so`.

---

## Quick Start

### Run All Phases
```bash
LD_PRELOAD=build/libspl_torch.so bin/simple examples/projects/medgemma_korean/run_all.spl
```

### Run Individual Phase
```bash
# Phase 0 only
LD_PRELOAD=build/libspl_torch.so bin/simple examples/projects/medgemma_korean/src/train_phase0.spl

# Phase 0 + 1
LD_PRELOAD=build/libspl_torch.so bin/simple examples/projects/medgemma_korean/src/train_phase1.spl

# Phase 0 + 1 + 2
LD_PRELOAD=build/libspl_torch.so bin/simple examples/projects/medgemma_korean/src/train_phase2.spl
```

---

## Directory Structure

```
medgemma_korean/
├── README.md                    # This file
├── run_all.spl                  # Complete pipeline (all 3 phases)
├── config/
│   ├── base.sdn                # Base configuration
│   ├── phase0.sdn              # Phase 0 config
│   ├── phase1.sdn              # Phase 1 config
│   └── phase2.sdn              # Phase 2 config
├── src/
│   ├── model.spl               # TextModel (3-layer feed-forward on CUDA)
│   ├── lora_utils.spl          # Real LoRA: A/B matrices, merge, freeze
│   ├── train_phase0.spl        # Phase 0: Plain text training
│   ├── train_phase1.spl        # Phase 1: Medical dict training
│   ├── train_phase2.spl        # Phase 2: MCQ training
│   └── validation.spl          # Real inference validation
├── data/ -> symlink             # Training data
├── old_py/ -> symlink           # Original Python implementation
└── models/                     # Output directory
```

---

## Architecture

### TextModel (src/model.spl)

Real 3-layer feed-forward network on CUDA:

```
Input [batch=16, dim=64]
  → Linear(64, 128) → GELU
  → Linear(128, 128) → GELU
  → Linear(128, 32)
  → Output [batch=16, dim=32]
```

All tensor operations run on CUDA GPU via libtorch FFI (`rt_torch_*` functions).

### LoRA (src/lora_utils.spl)

Real Low-Rank Adaptation:

```simple
# LoRA adds trainable A, B to frozen weight W:
# output = x @ W^T + (x @ A^T) @ B^T * (alpha / rank)

# A: [rank, in_features] - small random init
# B: [out_features, rank] - zero init (starts as identity)

# Merge: W_new = W + B @ A * scale
```

- **Rank**: 8 (configurable)
- **Alpha**: 16.0
- Applied to layers 1 and 2

### Training Loop

Real GPU training per step:
1. Generate batch on CUDA (`rt_torch_tensor_randn` → `rt_torch_torchtensor_cuda`)
2. Forward pass through model + LoRA (matmul, GELU activations)
3. MSE loss as differentiable tensor (for autograd backward)
4. `rt_torch_autograd_backward` computes gradients
5. Manual SGD: `param = param - lr * grad`
6. Zero gradients for next step

---

## What's Real

Everything uses actual CUDA GPU computation:

- **Tensors**: Created via `rt_torch_tensor_randn`, moved to GPU via `rt_torch_torchtensor_cuda`
- **Forward pass**: Real matrix multiplications (`rt_torch_torchtensor_matmul`), real activations (`rt_torch_torchtensor_gelu`)
- **Loss**: Real MSE computed as differentiable tensor operations
- **Backward**: Real autograd via `rt_torch_autograd_backward`
- **Gradients**: Real gradient tensors via `rt_torch_autograd_grad`
- **SGD update**: Real parameter updates (`param = param - lr * grad`)
- **LoRA merge**: Real matrix multiply (`W = W + B @ A * scale`)
- **Memory tracking**: Real GPU memory via `rt_torch_cuda_memory_allocated`

---

## Comparison: Python vs Simple

### Python (old_py/)
```python
# 20+ imports (transformers, peft, trl, torch, ...)
# HuggingFace model loading (AutoModelForCausalLM)
# BitsAndBytes 8-bit quantization
# PEFT LoRA adapter management
# SFTTrainer with callbacks
# ~600 lines per training script
```

### Simple (this implementation)
```simple
# Direct libtorch FFI (rt_torch_* functions)
# Real CUDA tensor operations
# Manual LoRA implementation (A, B matrices)
# Manual SGD optimizer
# ~150 lines per training script
```

---

## References

- **Torch FFI**: `src/lib/gc_async_mut/torch/` (Tensor, Linear, FFI bindings)
- **C++ Bridge**: `src/runtime/torch_ffi.cpp` (90+ libtorch wrappers)
- **Build Script**: `scripts/build/build-torch-ffi.sh`
- **Tests**: `test/unit/lib/torch_spec.spl`
- **Original Python**: `old_py/` (HuggingFace/PEFT implementation)
