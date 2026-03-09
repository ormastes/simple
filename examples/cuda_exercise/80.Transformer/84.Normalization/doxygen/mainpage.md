# Module 84: Normalization

## Overview

This module implements Root Mean Square Layer Normalization (RMSNorm) for transformer inference. RMSNorm simplifies standard LayerNorm by removing the mean-centering step, computing only the root mean square for normalization scaling. Both fp32 and fp16 variants are provided, with the fp16 kernel using fp32 internal accumulation for numerical stability.

## Key Components

- **rmsnorm.cu** -- RMSNorm kernel using `compute_rms_rsqrt` and `block_reduce_sum` from Module 88
- **rmsnorm.cuh** -- Public API declarations for `launch_rmsnorm` and `launch_rmsnorm_fp16`

## Dependencies

- Module 88 (Normalization_Common_API) -- warp/block reduction primitives
