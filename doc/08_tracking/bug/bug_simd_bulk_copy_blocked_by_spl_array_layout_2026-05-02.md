# Bug: SIMD Bulk Copy (J3 Rec 1) Blocked by SplArray<SplValue> Layout

**Date:** 2026-05-02
**Reporter:** Wave K / K2
**Severity:** Blocker for J3 Recommendation 1
**Related:** `doc/01_research/compress_simd_patterns_2026-05-02.md` §11 Rec 1, §12

---

## Summary

Two stop conditions from the K2 task brief fired during investigation.
J3 Recommendation 1 (SIMD bulk copy for `append_bytes` / `append_self_overlap_copy`) cannot be
implemented as described without changes to the Rust seed compiler.

---

## Stop Condition 1 — New extern requires Rust seed edit

Any new bulk-copy extern (`rt_simd_memcpy_chunk` or similar) must be registered in:
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` (Cranelift codegen signature table)
- `src/compiler_rust/compiler/src/interpreter_extern/ffi_array.rs` (interpreter dispatch)

Both files are Rust seed files. Adding a new extern to `src/runtime/runtime_native.c` alone is
not sufficient; the seed must also know the symbol and its calling convention.
Per task stop condition: *"simd_memcpy_chunk-equivalent extern requires Rust seed edit, not just
src/runtime/ — file bug doc + exit."*

## Stop Condition 2 — `_for_tier` dispatch is a no-op (capability detection fakes Scalar)

The existing `_for_tier` functions (`crc32_bytes_for_tier`, `xxhash32_bytes_for_tier`) dispatch on
`CompressionSimdTier` but all inner loops remain scalar. Example:

```
fn crc32_bytes_for_tier(data: [u8], tier: CompressionSimdTier) -> u32:
    val chunk_width = _compression_simd_chunk_width(tier)  # 32 for AVX2, 16 for NEON, 1 for scalar
    while idx + chunk_width <= data.len():
        var lane = 0
        while lane < chunk_width:
            crc = _crc32_update_byte(crc, data[idx + lane])  # still one byte per iteration
            lane = lane + 1
```

`chunk_width = 32` for AVX2 means 32 calls to `_crc32_update_byte` per "chunk" — identical
throughput to `chunk_width = 1` scalar. No SIMD intrinsics are wired.
Per task stop condition: *"The `_for_tier` dispatch turns out to actually be a no-op — note in
J3 follow-up bug doc + exit."*

---

## Root Cause: SplArray<SplValue> is not a packed byte buffer

`[u8]` in Simple is `SplArray*` — a heap-allocated array of `SplValue` (8-byte tagged unions).
`rt_bytes_from_raw` at `src/runtime/runtime_native.c:338` confirms this: it copies raw C bytes
into an SplArray by calling `spl_array_push_i64` per byte. Each byte occupies one 8-byte slot.

SIMD intrinsics (`_mm_loadu_si128`, `vld1q_u8`) require contiguous packed `uint8_t` memory.
They cannot operate on `SplArray<SplValue>`.

**Consequence:** the J3 §11 Rec 1 implementation plan (16-byte unaligned load+store loop) is
unreachable on the current data layout regardless of what C code is added to `src/runtime/`.

---

## Prerequisite for Fix

One of the following changes is needed before J3 Rec 1 can land:

**Option A — Packed byte buffer type**
Introduce a `Bytes` / `ByteVec` type backed by a plain `uint8_t*` heap allocation.
Register SIMD copy intrinsics over it. `[u8]` in compress hot paths migrates to this type.
Estimated scope: medium compiler change + migration of all `[u8]` callers in `src/lib/common/compress/`.

**Option B — Bulk-append extern over existing SplArray**
Add `rt_array_extend_i64(dst: SplArray*, src: SplArray*, start: i64, count: i64)` that loops
in C, amortising interpreter-dispatch overhead. No SIMD, but eliminates per-element Simple
dispatch. Expected 1.5–2× improvement on `append_bytes`/`append_bytes_range`.
Requires: one new extern in `runtime_native.c` + `runtime_ffi.rs` + `ffi_array.rs`.
No layout change needed.

---

## Secondary Bug: xxHash64 chunk_width dead NEON branch

**File:** `src/lib/common/compress/zstd.spl:1119`

```
val chunk_width = if tier == CompressionSimdTier.avx2: 32 else: 32
```

Both branches are `32`. The NEON branch is dead (NEON should use `16`).
This is the latent bug J3 noted in §12 Appendix. One-line fix:

```
val chunk_width = if tier == CompressionSimdTier.avx2: 32 else: 16
```

This fix is in scope as a small correctness repair (not in K2's core scope per task brief but
is the exact "small follow-up bug doc" J3 mentioned). See commit in this change.

---

## Pre-existing Test Failures (Baseline, Not K2 Regressions)

Recorded so the next agent does not chase these as new failures:

| Test file | Pass | Fail |
|-----------|------|------|
| `test/unit/lib/common/zstd_sequence_rle_spec.spl` | 5 | 1 ("decodes a one-sequence block with a normal offset") |
| `test/unit/lib/common/zstd_compressed_block_spec.spl` | 3 | 4 (UnsupportedFeature vs TruncatedInput) |

---

## Files Inspected

- `src/lib/common/compress/utilities.spl` — `append_bytes` (L144), `append_self_overlap_copy` (L160), `crc32_bytes_for_tier` (L191), `_compression_simd_chunk_width` (L182)
- `src/lib/common/compress/zstd.spl:1119` — xxHash64 chunk_width bug
- `src/runtime/runtime_native.c` — `SplArray*` layout, `rt_bytes_from_raw`
- `src/runtime/runtime.c` — `spl_array_push`, `spl_array_concat`
- `src/compiler_rust/compiler/src/interpreter_extern/ffi_array.rs` — extern registration
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` — Cranelift extern declaration
- `doc/01_research/compress_simd_patterns_2026-05-02.md` — J3 audit
