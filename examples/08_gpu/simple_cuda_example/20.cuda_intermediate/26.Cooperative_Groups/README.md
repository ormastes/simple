# Cooperative Groups

**Tier:** 3 (Skip)
**Status:** Not applicable to Simple

## Why Skipped

Cooperative groups are a CUDA-specific feature for flexible thread synchronization
beyond the traditional block-level `__syncthreads()`. This includes grid-level
synchronization, warp-level primitives, and dynamic group partitioning, all of which
are tightly coupled to NVIDIA's warp execution model.

In Simple, equivalent functionality is achieved through:
- **`sync_threads()`:** Block-level synchronization in `@gpu_kernel` functions
- **Atomic operations:** `atomic_add`, `atomic_cas` for inter-block coordination
- **Multi-kernel dispatch:** Separate kernel launches with device synchronization between them

## Original CUDA Exercise

See the original CUDA cooperative groups exercise for the NVIDIA-specific implementation
using `cooperative_groups::this_grid()`, `tiled_partition()`, and `grid_group::sync()`.

**Reference:** [NVIDIA Cooperative Groups](https://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#cooperative-groups)
