# Module 85: Tensor Operations

## Overview

This module provides core tensor manipulation kernels used throughout the transformer inference pipeline. It includes a fused bias + residual addition kernel and a shared-memory-optimized 2D matrix transpose.

## Key Components

- **bias_residual.cu** -- Fused kernel computing `output = input + bias[col] + residual`, reducing memory traffic by combining two element-wise operations into a single pass
- **transpose_permute.cu** -- Shared-memory transpose using 32x32 tiles with +1 column padding to eliminate bank conflicts

## Dependencies

- Module 89 (Tensor_Ops_Common_API) -- common tensor operation utilities
