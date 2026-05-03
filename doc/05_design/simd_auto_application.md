# Design: SIMD / Matrix / Bit-ISA Auto-Application

Date: 2026-05-03

## Implemented design decisions

### 1. Canonical intrinsic names

Added central MIR names for:

- `bit_rotate_left`
- `bit_rotate_right`
- `bit_popcount`
- `bit_clz`
- `bit_ctz`
- `bit_bswap`
- `bit_bitreverse`
- `crypto_clmul`
- `matrix_dot`
- `matrix_outer_product`
- `matrix_fma_kernel`

### 2. Capability classification

Added `TargetFeatureClass` for:

- `FixedWidthSimd`
- `ScalableSimd`
- `BitManip`
- `Crypto`
- `Matrix`

Per-backend helpers answer whether a planning class is supported and convert preferred vector width into lane counts.

### 3. Auto-vectorize recipe enrichment

`VectorRecipe` now carries:

- `index_locals`
- `store_value`

This keeps the future CFG splice and legality checks from having to rediscover basic memory operands.

### 4. Elementwise rewrite gate

The phase-1 rewrite set is:

- `add_elementwise`
- `sub_elementwise`
- `mul_elementwise`
- `xor_elementwise`

`div_elementwise` stays deferred.

### 5. Fast-math policy

- Elementwise FP rewrites are allowed without `fast_math`.
- FP reductions still require `fast_math` because they imply reassociation.

### 6. Matrix-kernel matching

The new matcher recognizes a conservative inner-loop shape:

- at least two loads
- one mul
- one add
- counted induction
- no calls

It emits a `MatrixKernel` recipe for logging/future lowering.

## Follow-up design work

- dedicated rewrite path for matrix kernels
- backend lowering for the new bitmanip intrinsic family
- real target-triple plumbing into MIR auto-vectorize
