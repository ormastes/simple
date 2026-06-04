# Training Infrastructure

**Tier:** 3 (Skip)
**Status:** Covered elsewhere in Simple

## Why Skipped

Training infrastructure (distributed training, data parallelism, gradient
accumulation, mixed-precision training, checkpointing) is covered by Simple's
`/deeplearning` skill and the `std.ml` module rather than being a standalone
GPU exercise.

Key Simple resources for training infrastructure:
- **`/deeplearning` skill:** Full ML pipeline operators and training patterns
- **`std.ml` module:** Built-in training loop, optimizers, schedulers
- **Exercise 72 (Backprop):** Gradient computation kernels
- **Exercise 27 (Multi-GPU):** Multi-device data parallelism

## Original CUDA Exercise

See the original CUDA training infrastructure exercise for distributed training
with NCCL, gradient all-reduce, and mixed-precision training with loss scaling.

**Reference:** For Simple's ML training approach, see the `/deeplearning` skill
documentation and `src/lib/gc_async_mut/` module.
