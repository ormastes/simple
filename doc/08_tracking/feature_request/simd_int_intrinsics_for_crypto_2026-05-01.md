# Feature: extend SIMD surface with int bitwise / rotate / shuffle ops for crypto

- **Date:** 2026-05-01
- **Status:** Proposed
- **Module:** `src/lib/nogc_sync_mut/simd.spl` + compiler HIR/codegen
- **Driver:** Phase 4 of the HTTPS/HTTP2 compression+cipher pass
  (`/home/ormastes/.claude/plans/see-next-and-impl-ethereal-scott.md`)

## Background

`src/lib/nogc_sync_mut/simd.spl` currently exposes:

- `Vec4f` (f32x4) with arithmetic, comparison, FMA, load/store, horizontal reductions, platform detection.
- `Vec4i` (i32x4) with `simd_add_i32x4`, `simd_sub_i32x4`, `simd_mul_i32x4`, plus splat / from_array / zero.
- `Vec8i` (i32x8) with the i32x8 equivalents.

The runtime crate does have AES-NI wiring (`src/compiler_rust/runtime/src/value/aes.rs` uses `_mm_aesenc_si128`, `_mm_aesenclast_si128`, `_mm_xor_si128`, `__m128i`, `_mm_loadu_si128`, `_mm_storeu_si128`), but those primitives are **not exposed to Simple-language code as SIMD intrinsics**. They are reachable only via specific high-level routines that happen to use them internally.

## Gap

For pure-Simple SIMD-accelerated cryptography (ChaCha20, SHA-256/512, AES-GCM, Poly1305) the missing operations are:

| Op | Why we need it | Today |
|---|---|---|
| `simd_xor_i32x4` / `_i32x8` | ChaCha20 quarter-round, SHA round Σ-functions, GHASH bit-mixing | absent |
| `simd_and_i32x4` / `simd_or_i32x4` / `simd_not_i32x4` | SHA Ch/Maj functions, Poly1305 carry handling | absent |
| `simd_shl_i32x4(v, n: i64)` / `simd_shr_i32x4(v, n: i64)` (logical) | SHA message schedule (right shifts), ChaCha20 rotates (shl + shr + or) | absent |
| `simd_rotl_i32x4(v, n: i64)` | ChaCha20 quarter-round (RotL by 16/12/8/7) | absent (could synthesize as shl+shr+or) |
| `Vec16u8` (u8x16) type + `simd_xor_u8x16`, `simd_shuffle_u8x16(v, mask)` | AES round byte SubBytes (table-lookup via shuffle), AES-GCM byte ops | absent — Vec4i/Vec8i are i32-shaped, not u8-shaped |
| `simd_aes_round(state: Vec16u8, key: Vec16u8) -> Vec16u8` (`_mm_aesenc_si128` / `vaeseq_u8`) | AES single-round encryption, ~5–10× speedup over scalar tables | absent at Simple layer (exists in Rust runtime) |
| `simd_aes_round_last` (`_mm_aesenclast_si128`) | AES final round | absent at Simple layer |
| `simd_pclmul64(a: Vec2u64, b: Vec2u64, imm: i64) -> Vec2u64` | GHASH multiplication for AES-GCM | absent — `Vec2u64` doesn't exist either |

## Estimated speedup if we land these

| Primitive | Scalar baseline (rough) | Expected SIMD speedup | Real-world impact |
|---|---|---|---|
| ChaCha20 (1 KiB block) | 1.0× | 2–4× on AVX2/NEON | TLS bulk encryption on mobile/AArch64, modern HTTPS |
| SHA-256 (single block) | 1.0× | 1.3–1.5× via SIMD message schedule, 5–10× via dedicated SHA-NI | TLS handshake transcript hashing, JWT signing |
| SHA-512 (single block) | 1.0× | 1.5–2× via SIMD message schedule | TLS PRF, large-payload HMAC |
| AES-GCM (1 KiB) | 1.0× | 5–10× via AES-NI + PCLMULQDQ | TLS bulk encryption on x86_64, baseline server perf |
| Poly1305 (1 KiB) | 1.0× | 2–3× via SIMD lane parallelism | TLS bulk MAC, ChaCha20-Poly1305 throughput |

The biggest win is AES-GCM via AES-NI: pure-scalar AES-GCM is ~50–100 MB/s on a modern x86_64 CPU; AES-NI-accelerated is ~3–5 GB/s. For a server saturating its NIC this is the difference between TLS being CPU-bound and bandwidth-bound.

## Implementation sketch

This is a Simple-compiler-touching task, not a stdlib-only change. Implementation phases:

### Phase 1 — bitwise int intrinsics (smallest, unblocks ChaCha20 + SHA)

In `src/lib/nogc_sync_mut/simd.spl`:

```simple
extern fn rt_simd_xor_i32x4(a: Vec4i, b: Vec4i) -> Vec4i
extern fn rt_simd_and_i32x4(a: Vec4i, b: Vec4i) -> Vec4i
extern fn rt_simd_or_i32x4(a: Vec4i, b: Vec4i)  -> Vec4i
extern fn rt_simd_shl_i32x4(a: Vec4i, n: i64) -> Vec4i
extern fn rt_simd_shr_i32x4(a: Vec4i, n: i64) -> Vec4i

fn simd_xor_i32x4(a: Vec4i, b: Vec4i) -> Vec4i:
    rt_simd_xor_i32x4(a, b)
# ... and so on, plus i32x8 siblings.
```

In the runtime (`src/compiler_rust/runtime/src/value/`):

- Add a `simd_int_ops.rs` (or extend `value/`) with `_mm_xor_si128` / `_mm_and_si128` / `_mm_or_si128` for x86, `veorq_s32` / `vandq_s32` / `vorrq_s32` for AArch64, scalar fallback.
- Wire each `rt_simd_xor_i32x4` etc. into the FFI table.
- HIR / interpreter-extern resolution for the new symbols.

Once this lands, ChaCha20 and SHA-256 can be vectorized in pure Simple in an afternoon each (Phase 4b/4c of the parent plan).

### Phase 2 — `Vec16u8` + AES intrinsics (AES-GCM acceleration)

- Add `Vec16u8` struct (16 bytes addressable as 4×u32 internally; type-tag distinguishes from `Vec4i`).
- Add `simd_xor_u8x16`, `simd_shuffle_u8x16(v, mask: Vec16u8)`.
- Add `simd_aes_round(state: Vec16u8, key: Vec16u8) -> Vec16u8` and `simd_aes_round_last`.
- Runtime maps to `_mm_aesenc_si128` / `_mm_aesenclast_si128` on x86_64, `vaeseq_u8` + `vaesmcq_u8` on AArch64.
- Scalar fallback: byte-wise S-box + ShiftRows + MixColumns.
- AES-NI feature detection: caller code branches via `has_aes_ni()` similar to existing `has_avx2()`.

### Phase 3 — `Vec2u64` + PCLMUL (GHASH acceleration)

- Add `Vec2u64` (2×u64).
- Add `simd_pclmul64(a: Vec2u64, b: Vec2u64, imm: i64) -> Vec2u64`.
- Runtime maps to `_mm_clmulepi64_si128` on x86_64; ARMv8.2-A `vmull_p64` on AArch64; scalar fallback (Karatsuba).
- This unblocks the GHASH part of AES-GCM, which is otherwise the bottleneck even with AES-NI on the cipher side.

## Workaround until landed

`src/os/crypto/aes_gcm.spl`, `chacha20.spl`, `sha256.spl` etc. continue to use scalar implementations. Performance is 5–50× slower than C/Rust libraries with AES-NI/AVX2, but functionality is correct. For HTTP server use cases under low concurrent load this is acceptable; for high-throughput production HTTPS it is not.

The Phase 1 compression dispatcher and Phase 2 HPACK work (currently in progress) do not depend on this — they're not crypto. Only Phase 4 of the parent plan depends on this feature.

## Cross-references

- Plan: `/home/ormastes/.claude/plans/see-next-and-impl-ethereal-scott.md` — Phase 4
- Existing SIMD stdlib: `src/lib/nogc_sync_mut/simd.spl` (~370 lines as of 2026-05-01)
- Existing AES runtime hook: `src/compiler_rust/runtime/src/value/aes.rs` (uses AES-NI but does not expose it as a SIMD intrinsic)
- Crypto modules that would benefit: `src/os/crypto/{aes_gcm,chacha20,chacha20_poly1305,sha256,sha512,poly1305}.spl`
