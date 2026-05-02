# FR: Vec4u32 and Vec4i64 SIMD Intrinsics
# Wave L / L4 — 2026-05-02

## Summary

Add `rt_simd_*_u32x4` (8 ops) and `rt_simd_*_i64x4` (8 ops) extern primitives
to the Rust runtime, with corresponding `.spl` wrapper functions and type alias
declarations in `src/lib/nogc_sync_mut/simd/aliases.spl`.

## Context

Wave L4 surveyed Vec4i-compatible targets (see
`doc/01_research/vec4i_compat_targets_2026-05-02.md`).  The alias conditions
require Rust-seed externs before any alias can land:

- `Vec4u32` alias requires `simd_*_u32x4` externs — none exist today
  (`grep "simd_.*u32x4" src/lib/nogc_sync_mut/simd.spl` returns empty).
- `Vec4i64` alias requires `simd_*_i64x4` externs (256-bit AVX2/SVE2) — none
  exist today.

Note: `Vec4u = FixedVec<u32>` is already declared at
`src/lib/nogc_sync_mut/simd/aliases.spl:52`.  `Vec4u32` would be an additional
name for the same lane shape; it is not a priority alias, but the underlying
primitives ARE needed (see Rationale).

## Rationale

### Vec4u32 (4 × u32, 128-bit)

The Salsa20 and ChaCha20 ARX kernels use `u32` arithmetic.  The current
`Vec4i` workaround (`_u32_to_i32` / `_i32_to_u32` cast helpers in
`src/lib/common/crypto/chacha20.spl:64-75`) is bit-exact but requires two
casts per accumulation.  Native `u32x4` arithmetic would:

- Eliminate the cast helpers entirely
- Avoid signed-overflow UB concerns in future backends
- Enable a direct `simd_add_u32x4` for ChaCha20/Salsa20 without struct-field
  fallback (the current Phase 1 workaround uses struct-field arithmetic instead
  of `rt_simd_add_i32x4` because the add was "declared but UNWIRED" per
  `src/lib/common/crypto/chacha20.spl:16-17`)

Required ops (mirrors the i32x4 set at `simd.spl:350-387`):

```
rt_simd_add_u32x4(a, b)   rt_simd_sub_u32x4(a, b)
rt_simd_mul_u32x4(a, b)   rt_simd_xor_u32x4(a, b)
rt_simd_and_u32x4(a, b)   rt_simd_or_u32x4(a, b)
rt_simd_shl_u32x4(a, n)   rt_simd_shr_u32x4(a, n)
```

Hardware mapping: `_mm_add_epi32` / `vaddq_u32` — same instruction as i32x4
(integer SIMD doesn't distinguish signed/unsigned for add/sub/bitwise).
Only `mul` differs on some backends (`_mm_mullo_epi32` vs unsigned semantics).

### Vec4i64 (4 × i64, 256-bit)

`Vec4i64` maps to AVX2 `__m256i` (x86) or a pair of `int64x2_t` (AArch64 NEON).
Primary use cases:

- SHA-512 / SHA-384 message schedule and round compression (64-bit word ops)
- Future BLAKE2b (64-bit ARX)
- Large-integer / bignum limb arithmetic

Required ops (8, matching the i32 pattern):

```
rt_simd_add_i64x4(a, b)   rt_simd_sub_i64x4(a, b)
rt_simd_mul_i64x4(a, b)   rt_simd_xor_i64x4(a, b)
rt_simd_and_i64x4(a, b)   rt_simd_or_i64x4(a, b)
rt_simd_shl_i64x4(a, n)   rt_simd_shr_i64x4(a, n)
```

## Proposed Implementation

1. **Rust seed** (`src/compiler_rust/` — DO NOT touch in `.spl` waves):
   - Add 16 new `rt_simd_*` extern handlers for u32x4 and i64x4 lane types.
   - Reuse existing `Vec4i` struct layout; add `Vec4u32` and `Vec4i64` structs
     (4 × u32 / 4 × i64 fields).

2. **simd.spl** (`src/lib/nogc_sync_mut/simd.spl`):
   - Add `struct Vec4u32` and `struct Vec4i64` (mirrors `Vec4i` at line 193).
   - Declare 8 `extern fn rt_simd_*_u32x4` + 8 `extern fn rt_simd_*_i64x4`.
   - Add `.spl` wrapper functions (`simd_add_u32x4`, etc.).

3. **aliases.spl** (`src/lib/nogc_sync_mut/simd/aliases.spl`):
   - Add `type Vec4u32 = FixedVec<u32>` (inert until D3/E2, same as existing
     `Vec4u` at line 52).
   - Add `type Vec4i64 = FixedVec<i64>`.
   - Add `vec4u32_splat` / `vec4i64_splat` constructor wrappers.

## Related

- `src/lib/nogc_sync_mut/simd.spl:350-387` — existing i32x4 pattern to follow
- `src/lib/nogc_sync_mut/simd/aliases.spl:47-53` — existing alias declarations
- `doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md`
  — Phase 2 (u8x16) and Phase 3 (u64x2/PCLMUL) FRs
- `doc/01_research/vec4i_compat_targets_2026-05-02.md` — survey that uncovered
  the gap

## Priority

MEDIUM.  The current `Vec4i` workaround in ChaCha20 is bit-exact and the
cast overhead is small.  However, `Vec4i64` is a blocker for SHA-512 SIMD
(which has no current workaround at all).

## Bootstrap Note

After adding Rust-seed externs: run
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (not `bin/simple build
bootstrap` — `build` falls through the wrapper whitelist and silently no-ops
per memory note `feedback_extern_bootstrap_rebuild.md`).
