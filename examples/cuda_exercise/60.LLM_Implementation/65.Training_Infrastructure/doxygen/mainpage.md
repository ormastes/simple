# Module 65: Training Infrastructure

## Overview

This module implements the core training infrastructure for GPU-accelerated LLM training, including the AdamW optimizer, learning rate schedulers, loss functions, and gradient manipulation utilities.

Based on "LLMs from Scratch" by Sebastian Raschka (Chapter 5) and standard practices from GPT-2/GPT-3 training.

## Architecture

The module is organized into the following components:

### Optimizer (host/ + kernels/)
- **AdamW Optimizer**: Decoupled weight decay regularization with bias-corrected moment estimates
- **Fused GPU Kernel**: Single-kernel parameter update for maximum throughput

### Learning Rate Schedulers (host/)
- **Constant**: Fixed learning rate
- **CosineAnnealing**: Cosine decay from base_lr to min_lr
- **WarmupCosine**: Linear warmup followed by cosine decay (standard for GPT)
- **LinearWarmup**: Linear warmup followed by constant lr

### Loss Functions (kernels/)
- **CrossEntropyLoss**: Numerically stable log-softmax + NLL for language modeling
- **MSELoss**: Mean squared error for regression tasks
- **GRPO Reward**: Group Relative Policy Optimization for reasoning training (placeholder)

### Gradient Utilities (kernels/)
- **Gradient Clipping**: Clip by global L2 norm to prevent exploding gradients
- **Gradient Accumulation**: Accumulate gradients across micro-batches
- **Gradient Zeroing**: Reset accumulator between steps

## Key APIs

### Optimizer
- @ref llm::adamw_step() - Perform one AdamW parameter update on GPU
- @ref llm::allocate_adamw_state() - Allocate optimizer moment buffers
- @ref llm::free_adamw_state() - Release optimizer state

### Learning Rate
- @ref llm::LRScheduler::get_lr() - Get learning rate for a given step
- @ref llm::cosine_annealing_lr() - Cosine decay computation
- @ref llm::warmup_cosine_lr() - Warmup + cosine decay computation

### Loss
- @ref llm::cross_entropy_loss() - Cross-entropy loss for language modeling
- @ref llm::mse_loss() - Mean squared error loss

### Gradients
- @ref llm::gradient_clip_by_norm() - Clip gradients by global norm
- @ref llm::gradient_accumulate() - Accumulate micro-batch gradients

## Testing

Comprehensive unit tests in `test/unit/`:
- `test_training_loop.cpp`: Training configuration and scheduler tests
- `test_adamw.cu`: AdamW optimizer kernel correctness tests
- `test_loss.cu`: Cross-entropy and MSE loss verification
- `test_gradients.cu`: Gradient clipping and accumulation tests

## References

- [Decoupled Weight Decay Regularization (AdamW)](https://arxiv.org/abs/1711.05101)
- [LLMs from Scratch - Chapter 5](https://github.com/rasbt/LLMs-from-scratch)
- [DeepSeek R1 - GRPO Training](https://arxiv.org/abs/2501.12948)
