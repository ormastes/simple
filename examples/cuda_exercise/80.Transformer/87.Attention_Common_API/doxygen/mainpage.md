# Module 87: Attention Common API

## Overview

This module provides reusable primitives for scaled dot-product attention (SDPA) kernels used throughout the transformer inference stack. These building blocks are consumed by Module 82 (Attention Kernels) to implement FlashAttention and related algorithms.

## Module Architecture

The module is organized into the following components:

- **common/sdpa_tiles**: Tile shape configurations and shared memory size calculations for different GPU architectures (SM75, SM80, SM86). These constants define the blocking strategy for tiled attention.

- **common/online_softmax**: Numerically stable streaming softmax that computes row-wise softmax in a single pass without materializing the full N x N attention matrix. Includes state update, merge (for parallel reduction), finalize, and rescale operations.

- **common/causal_mask**: Predicate functions for autoregressive (causal) masking. Supports element-level and tile-level checks, including fast-path optimizations for tiles that are fully masked or fully unmasked.

- **common/qkv_packing**: Layout reordering kernels to convert between [B,T,H,D] (natural token-interleaved) and [B,H,T,D] (head-grouped computation) tensor layouts for multi-head attention.

## Key Components

### SDPA Tile Configuration
- `SDPATileConfig` struct with Br, Bc, D fields
- Architecture-specific defaults: `sdpa_tile_sm75()`, `sdpa_tile_sm80()`, `sdpa_tile_sm86()`
- `sdpa_smem_size()` for computing shared memory requirements

### Online Softmax
- `SoftmaxState` with running max and sum of exponentials
- `online_softmax_update()` for incremental value incorporation
- `online_softmax_merge()` for parallel reduction of partial states
- `online_softmax_finalize()` for computing final probabilities
- `online_softmax_rescale()` for adjusting accumulated PV products

### Causal Masking
- `causal_keep()` / `apply_causal_mask()` for element-level masking
- `tile_causal_keep()` / `tile_fully_masked()` / `tile_fully_unmasked()` for tile-level optimization

### QKV Packing
- `bthd_to_bhtd` / `bhtd_to_bthd` kernels for layout transposition
- `reorder_bthd_to_bhtd()` / `reorder_bhtd_to_bthd()` host launch wrappers

## Usage Examples

See the `test/` directory for comprehensive usage examples:

- `test/unit/kernels/test_online_softmax.cu`: Validates online softmax against CPU reference
- `test/unit/kernels/test_causal_mask.cu`: Tests masking predicates for correctness
- `test/unit/kernels/test_qkv_packing.cu`: Tests layout roundtrip for various dimensions

## Building Documentation

From the build directory:
```bash
ninja doxygen_87_Attention_Common_API
```

The generated HTML documentation will be available at:
```
build/80.Transformer/87.Attention_Common_API/doxygen/html/index.html
```

## Dependencies

- `CudaCustomLib` (cuda_utils.h)
- CUDA Runtime (cuda_runtime.h)

## See Also

- Module 82 (Attention Kernels) for FlashAttention implementation that consumes these primitives
- Module 88 (Normalization Common API) for warp/block reduction building blocks
- Module 89 (Tensor Ops Common API) for vectorized I/O utilities
