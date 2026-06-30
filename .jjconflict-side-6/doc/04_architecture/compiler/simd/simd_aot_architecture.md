# SIMD AOT Architecture

The SIMD pipeline spans the full compiler stack, from user-facing types in `00.common` through MIR optimization to Cranelift AOT code generation and runtime dispatch.

## Pipeline Overview

```
User code (std.simd API)
    |
    v
00.common/simd_types.spl     -- SimdElementType, FixedVecType, ScalableVecType, MaskType
    |
    v
30.types/simd*.spl            -- Type checking, platform capabilities, vector type validation
    |
    v
35.semantics/simd_check.spl   -- Semantic analysis, opportunity lint
    |
    v
50.mir/mir_instructions.spl   -- MIR SIMD opcodes (including masked/predicated)
    |
    v
60.mir_opt/simd_lowering.spl  -- Lowers intrinsic calls to MIR SIMD instructions
    |
    v
70.backend/x86_64_simd.spl   -- Cranelift AOT code generation
    |
    v
runtime (Rust)                -- x86 SSE2/AES-NI, AArch64 NEON, scalar fallback
```

## SIMD Type System (00.common)

Defined in `src/compiler/00.common/simd_types.spl`. Placed in `00.common` to avoid backward dependency from `35.semantics` to `50.mir`.

### Core Types

- **`SimdElementType`** -- 12-variant element type enum for cross-ISA type checking: `I8`, `I16`, `I32`, `I64`, `U8`, `U16`, `U32`, `U64`, `F16`, `F32`, `F64`, `BF16`
- **`FixedVecType`** -- compile-time-fixed lane count. `N` must be power-of-two >= 2 (validated by `simd_validate_lanes`)
- **`ScalableVecType`** -- runtime-determined lane count (SVE2 / RVV). `vscale_min` gives compile-time lower bound for unroll decisions. LMUL is hidden in the backend MIR pass
- **`SimdVecKind`** -- discriminated union over `FixedVecType` and `ScalableVecType`
- **`MaskType`** -- parameterized by its associated vector type, preserving lane-count and element-type in the IR

### Operations

- **`SimdBinop`** -- binary ops: `Add`, `Sub`, `Mul`, `Div`, `Fma`, `CmpEq`, `CmpLt`, `CmpLe`, etc.
- **`SimdUnop`** -- unary ops
- **`SimdReduceOp`** -- horizontal reductions
- **`SimdShuffleKind`** -- permutation / interleave operations
- **`SimdMaskMode`** -- three predication modes matching ARM SVE and RVV conventions
- **`SimdCmpKind`** -- comparison predicates
- **`SimdMaskOpKind`** -- mask-to-mask operations
- **`WarpShflKind`** / **`WarpReduceOp`** -- GPU warp operations (separated from SimdBinop)

### Validation

- `simd_validate_lanes(N)` -- rejects `N=0`, `N=1`, and non-power-of-two with `E_SIMD_BAD_LANES`
- `simd_lanes_preferred(arch, elem)` -- returns natural register width / elem width for fixed-width ISAs; minimum useful N for scalable ISAs

## Vec16u8 Type and Struct Layout

`Vec16u8` is a 16-byte vector of unsigned 8-bit integers, used primarily for AES cryptographic operations. It exists in the Rust runtime layer, not as a user-facing Simple type.

**Current ABI state:**

- AES round ops (`rt_simd_aes_round_u8x16`, `rt_simd_aes_round_last_u8x16`) use `RuntimeValue` handles with `to_raw()`/`from_raw()` (bit-preserving, no tagging) for Vec16u8 marshalling
- Basic byte ops (`rt_simd_add_u8x16`) still use the lane-array-shaped scalar ABI (33 args: 16 input lanes A + 16 input lanes B + dest pointer) pending full Vec16u8 marshalling layer

## MIR Masked/Predicated Opcodes (50.mir)

Defined in `src/compiler/50.mir/mir_instructions.spl`. These are the SIMD-specific MIR instructions:

### Mask Creation

- `MaskFromCmp(dest, cmp_kind, a, b)` -- produces a mask from a scalar comparison

### Masked Operations (inactive lanes controlled by mask)

- `MaskedAdd(dest, mask, a, b)` -- masked vector addition
- `MaskedMul(dest, mask, a, b)` -- masked vector multiplication
- `MaskedFma(dest, mask, a, b, c)` -- masked fused multiply-add (3 source operands + mask)

### Predicated Operations (fused MaskFromCmp + Masked)

These are the fused form after `predicate_promote` optimization:

- `PredicatedAdd(dest, cmp_kind, cmp_a, cmp_b, a, b)` -- k-register predicated addition
- `PredicatedMul(dest, cmp_kind, cmp_a, cmp_b, a, b)` -- k-register predicated multiplication
- `PredicatedFma(dest, cmp_kind, cmp_a, cmp_b, a, b, c)` -- k-register predicated fused multiply-add

The predicate_promote pass in `src/compiler/60.mir_opt/mir_opt/predicate_promote.spl` fuses separate `MaskFromCmp` + `Masked*` sequences into single `Predicated*` instructions.

## SIMD Lowering Pass (60.mir_opt)

`src/compiler/60.mir_opt/mir_opt/simd_lowering.spl` transforms high-level SIMD intrinsic calls into low-level MIR SIMD instructions:

```
Before: Call(dest: r1, func: rt_simd_add_f32x4, args: [a, b])
After:  SimdAddF32x4(dest: r1, a: Copy(a), b: Copy(b))
```

Runs after MIR construction but before optimization passes, allowing SIMD operations to participate in CSE, constant folding, etc.

## Interpreter Dispatch Path

The interpreter does NOT call `extern "C"` symbols. Instead it dispatches through `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`, which calls the lane kernels directly. This avoids the FFI overhead and ABI constraints of the compiled path.

## Cranelift AOT Path

### RuntimeValue ABI

The Cranelift AOT path uses `RuntimeValue` for Vec16u8 marshalling in AES operations:

- **`to_raw()`** -- bit-preserving extraction of the raw i64 value. The raw bits are a pointer to `rt_alloc`-ed memory containing 16 bytes
- **`from_raw()`** -- bit-preserving construction of a RuntimeValue from a raw i64

**IMPORTANT:** The code uses `to_raw()`/`from_raw()` (bit-preserving), NOT `as_int()`/`from_int()`. The latter would apply tag shifting (right-shift by 3 for extraction, left-shift by 3 for construction), which corrupts pointer values. Vec16u8 handles are untagged pointers stored in i64 vregs.

### Registration

SIMD runtime functions are registered in `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs`:

```rust
RuntimeFuncSpec::new("rt_simd_aes_round_u8x16", &[I64, I64], &[I64]),
RuntimeFuncSpec::new("rt_simd_aes_round_last_u8x16", &[I64, I64], &[I64]),
```

All `rt_simd_*` functions are classified as `Ext` tier (external/extension).

## Runtime Implementations

### x86_64 AES-NI (`src/compiler_rust/runtime/src/value/simd_aes_ops.rs`)

AES round semantics match Intel's intrinsics:

- `aes_round_u8x16(state, key)` = `MixColumns(SubBytes(ShiftRows(state))) XOR key` -- maps to `_mm_aesenc_si128`
- `aes_round_last_u8x16(state, key)` = `SubBytes(ShiftRows(state)) XOR key` -- maps to `_mm_aesenclast_si128`

Gated by `is_x86_feature_detected!("aes")` at runtime.

### AArch64 NEON (`src/compiler_rust/runtime/src/value/simd_aes_ops.rs`)

Uses `vaeseq_u8(state, 0)` which performs `ShiftRows(SubBytes(state))` after XOR with second arg. Zero is passed so the XOR with key happens after, matching the Intel ordering (standard x86/ARM AES asymmetry). `vaesmcq_u8` adds MixColumns for regular rounds; last round skips it.

### x86_64 SSE2 (`src/compiler_rust/runtime/src/value/simd_byte_ops.rs`)

Byte addition uses `_mm_add_epi8` (SSE2 is the x86_64 baseline). AArch64 uses `vaddq_u8`.

### Scalar Fallback

All operations have scalar fallbacks:

- Byte addition: `wrapping_add` per lane (carry does NOT leak across lane boundaries)
- AES rounds: ShiftRows -> SubBytes -> (MixColumns) -> XOR key, sharing `aes::SBOX`

## User-Facing SIMD API

`src/lib/nogc_sync_mut/simd.spl` provides the platform-independent SIMD API:

```
use std.simd.{Vec4f, simd_add_f32x4, simd_mul_f32x4}
val a = Vec4f.splat(2.0)
val b = Vec4f.splat(3.0)
val c = simd_add_f32x4(a, b)  # [5.0, 5.0, 5.0, 5.0]
```

**Operations:** arithmetic (add, sub, mul, div, fma), comparison (eq, ne, lt, le, gt, ge), load/store (from_array, to_array, load_aligned, store_aligned), reductions (horizontal_add, horizontal_max, horizontal_min).

**Platform detection:** `has_avx2`, `has_neon`, `simd_width`.

**Sub-modules** (`src/lib/nogc_sync_mut/simd/`): `vector.spl`, `mask.spl`, `aliases.spl`, `fixed.spl`, `scalable.spl`, `profile.spl`.

## File Index

| Path | Purpose |
|------|---------|
| `src/compiler/00.common/simd_types.spl` | Core SIMD type definitions |
| `src/compiler/30.types/simd.spl` | SIMD type checking |
| `src/compiler/30.types/simd_platform.spl` | Platform-specific SIMD capabilities |
| `src/compiler/30.types/simd_vector_types.spl` | Vector type validation |
| `src/compiler/30.types/simd_capabilities.spl` | ISA capability detection |
| `src/compiler/35.semantics/simd_check.spl` | Semantic SIMD validation |
| `src/compiler/35.semantics/lint/simd_opportunity_lint.spl` | Advisory lint for SIMD opportunities |
| `src/compiler/50.mir/mir_instructions.spl` | MIR SIMD opcodes |
| `src/compiler/60.mir_opt/mir_opt/simd_lowering.spl` | Intrinsic call -> MIR lowering |
| `src/compiler/70.backend/backend/native/x86_64_simd.spl` | x86_64 Cranelift SIMD codegen |
| `src/compiler/90.tools/fix/rules/impl/lint_simd.spl` | SIMD lint fix rules |
| `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` | Runtime function registration |
| `src/compiler_rust/compiler/src/interpreter_extern/simd.rs` | Interpreter SIMD dispatch |
| `src/compiler_rust/runtime/src/value/simd_byte_ops.rs` | Byte vector operations (SSE2/NEON/scalar) |
| `src/compiler_rust/runtime/src/value/simd_aes_ops.rs` | AES round intrinsics (AES-NI/NEON/scalar) |
| `src/lib/nogc_sync_mut/simd.spl` | User-facing SIMD API |
| `src/lib/nogc_sync_mut/simd/*.spl` | SIMD sub-modules |
| `src/lib/gc_async_mut/gpu/engine2d/simd_kernels.spl` | Engine2D SIMD kernels |
| `src/lib/gc_async_mut/gpu/engine3d/simd_kernels3d.spl` | Engine3D SIMD kernels |
