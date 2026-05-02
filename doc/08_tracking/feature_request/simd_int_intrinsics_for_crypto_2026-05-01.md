# Feature: extend SIMD surface with int bitwise / rotate / shuffle ops for crypto

> **AES-256 SIMD path LANDED 2026-05-02 — 14 rounds via W6-A externs.** `aes256_encrypt_block` in `src/os/crypto/aes256_gcm.spl` now wires through `simd_aes_round` (×13) + `simd_aes_round_last` (×1), reusing the W6-A Phase 2 externs `rt_simd_aes_round_u8x16` / `rt_simd_aes_round_last_u8x16`. No new runtime extern. AES-256 round kernel is byte-identical to AES-128's; only round count (14 vs 10) and key schedule (240 B vs 176 B) differ. `gctr256` hoists `aes256_key_expansion(key)` out of the per-block loop for amortized cost. Commits: `7a0cd3a` (encrypt_block via SIMD path), `8d30036` (gctr256 hoist), `2201055` (FIPS 197 §C.3 + NIST SP 800-38A F.1.5 ECB byte-exact spec — 6/6 PASS in interpreter; also fixes a latent dispatcher type bug by switching `_load_round_key_v` and the new `_load_block_v` to feed `rt_bytes_u8_at` directly into the Vec16u8 constructor instead of going through `_u8_at`, since the runtime SIMD dispatcher's `unpack_vec16u8` requires `Value::Int` lane fields, not `Value::UInt{width:8}`). Spec file: `test/unit/lib/crypto/aes256_simd_round_spec.spl`. Existing `aes256_gcm_nist_vectors_spec.spl` and `simd_aes_ops_spec.spl` (5/5) unchanged.

> **Phase 2 AES-NI intrinsics LANDED 2026-05-01 — `simd_aes_round` + `simd_aes_round_last`.** Round-level primitives matching Intel `_mm_aesenc_si128` / `_mm_aesenclast_si128` ordering: `state -> ShiftRows -> SubBytes -> MixColumns (regular only) -> XOR key`. x86_64 AES-NI (runtime-detected via `is_x86_feature_detected!("aes")`), AArch64 NEON (`vaeseq_u8` + `vaesmcq_u8` with the standard XOR-first-vs-XOR-last asymmetry handled by feeding zero as AESE's second arg), and a scalar fallback that reuses `aes::SBOX` (no S-box duplication; `const SBOX` made `pub(crate)` for cross-module use). Files:
> - `src/lib/nogc_sync_mut/simd.spl` — `extern fn rt_simd_aes_round_u8x16` + `extern fn rt_simd_aes_round_last_u8x16` + pure-Simple `simd_aes_round` / `simd_aes_round_last` wrappers.
> - `src/compiler_rust/runtime/src/value/simd_aes_ops.rs` — NEW. `aes_round_u8x16` / `aes_round_last_u8x16` lane kernels + `extern "C"` symbols. 4 internal Rust unit tests (FIPS 197 §B round-1 KAT, ShiftRows known-vector, last-round S-box check; all PASS).
> - `src/compiler_rust/compiler/src/interpreter_extern/simd.rs` — handler functions reuse the Phase 2 seed `binop_u8x16` + `unpack_vec16u8` / `pack_vec16u8` plumbing.
> - `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — 2 dispatch arms.
> - `src/compiler_rust/common/src/runtime_symbols.rs` — 2 allowlist entries (already covered by the existing `rt_simd_` prefix tier classification).
> - Spec: `test/unit/lib/nogc_sync_mut/simd_aes_ops_spec.spl` (5 examples, 0 failures in seed-binary interpreter mode). FIPS 197 Appendix B AES-128 single-block KAT walked round-by-round (R1, R2, R9 via `simd_aes_round`, R10 ciphertext via `simd_aes_round_last` — all byte-exact). 11 round keys hardcoded so the spec exercises the round step in isolation, with key expansion deliberately not invoked (lives in `aes.rs` and stays scalar). Rounds 3..8 are computed implicitly when chaining to R9.

> **Phase 2 seed (Vec16u8 + simd_add_u8x16) LANDED 2026-05-01** — `simd_aes_round` / PCLMUL / shuffle deferred to follow-up waves (those need full AES-NI exposure or different intrinsics). See:
> - `src/lib/nogc_sync_mut/simd.spl` — `Vec16u8` struct (16 u8 fields `u0..u7,u8_,u9..u15`; `u8_` disambiguates the `u8` type-keyword clash) + `splat`/`from_array`/`zero`/`to_array` + `extern fn rt_simd_add_u8x16` + pure-Simple `simd_add_u8x16` wrapper.
> - `src/compiler_rust/runtime/src/value/simd_byte_ops.rs` — `add_u8x16` lane kernel (SSE2 `_mm_add_epi8` / NEON `vaddq_u8` / scalar `wrapping_add` fallback) + `extern "C" fn rt_simd_add_u8x16`. 4 internal Rust unit tests.
> - `src/compiler_rust/compiler/src/interpreter_extern/simd.rs` — `Vec16u8` unpack/pack helpers + `binop_u8x16` + `rt_simd_add_u8x16` handler.
> - `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` — dispatch arm.
> - `src/compiler_rust/common/src/runtime_symbols.rs` — allowlist entry.
> - Spec: `test/unit/lib/nogc_sync_mut/simd_byte_ops_spec.spl` (8 examples, 0 failures in interpreter mode). Carry-isolation property verified: `0xFF+0x01=0x00` per-lane, lane 1 stays 0 (no carry-in absorbed); `0xFF+0xFF=0xFE` across all 16 lanes.

> **Update 2026-05-01 (ChaCha20):** ChaCha20 vectorization landed — see `src/os/crypto/chacha20.spl` `chacha20_block4_simd` / `chacha20_encrypt_simd` (vertical 4-block parallel layout: lane k = block counter+k; 16 Vec4i state words; bitwise/rotate via `simd_xor/and/or/shl/shr_i32x4`; adds via direct Vec4i field arithmetic since Phase 1 did not wire `rt_simd_add_i32x4`). Parity spec: `test/unit/os/crypto/chacha20_simd_parity_spec.spl` (6/6 PASS, byte-exact vs scalar across 114 B / 256 B / 600 B / 1024 B; published RFC 8439 §2.4.2 ciphertext bytes match; round-trip recovers plaintext). Existing scalar KAT (`test/system/os_crypto_ref_primitives_spec.spl`, 33/33 PASS) unchanged. Interpreter-mode bench (1.7×–1.8× speedup at small sizes, 1.33× at 4 KiB): 256 B 12.4ms scalar / 7.1ms SIMD; 1 KiB 54.4ms scalar / 31.4ms SIMD; 4 KiB 374ms scalar / 280ms SIMD. (64 KiB exceeds the 60s interpreter watchdog at this throughput; revisit in compiled mode.) Full speedup is bounded by the bitwise/rotate fraction; wiring `rt_simd_add_i32x4` (5-line plumbing — symbol allowlist + interpreter dispatch arm + reuse existing scalar/SSE2/NEON kernel pattern) would also remove the lane-extract cost in adds.

> **Update 2026-05-01:** SHA-256 message-schedule vectorization landed using Phase 1 int intrinsics (xor + logical shifts on Vec4i). σ0 is computed 4-at-a-time per chunk; σ1 / round function / `add_mod32` chain remain scalar. Source: `src/lib/common/crypto/sha256.spl` (`sha256_little_sigma0_x4`, `sha256_process_block_simd`). Parity spec: `test/unit/lib/common/crypto/sha256_simd_parity_spec.spl` (7/7 PASS, byte-exact vs scalar; FIPS 180-4 NIST KAT vectors still PASS in `test/unit/lib/crypto/sha2_nist_vectors_spec.spl`). Interpreter-mode bench: SIMD path is ~1–6% slower than scalar due to extern dispatch + Vec4i marshalling overhead (1 KiB×5: 930ms SIMD / 920ms scalar; 64 KiB×1: 66.0s SIMD / 62.3s scalar). Re-bench in compiled mode is a follow-up once Vec4i FFI marshalling lands per the runtime_ffi.rs note below.

- **Phase 1 status: LANDED 2026-05-02** — 10 ops (xor/and/or/shl/shr × i32x4 + i32x8).
  - Pure-Simple wrappers + externs: `src/lib/nogc_sync_mut/simd.spl`
  - Runtime kernels: `src/compiler_rust/runtime/src/value/simd_int_ops.rs`
    (SSE2 / AVX2 / NEON intrinsics + scalar fallback; shift count masked to 0..=31).
  - Interpreter-extern dispatch + Vec4i/Vec8i marshalling:
    `src/compiler_rust/compiler/src/interpreter_extern/simd.rs` and
    `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.
  - Symbol allowlist: `src/compiler_rust/common/src/runtime_symbols.rs`.
  - Spec: `test/unit/lib/nogc_sync_mut/simd_int_ops_spec.spl` (14 examples, 0 failures
    in interpreter mode).
  - **Update 2026-05-01 (add/sub/mul backfill):** the pre-existing
    `rt_simd_{add,sub,mul}_i32x{4,8}` extern declarations are now wired
    end-to-end. Runtime kernels added in
    `src/compiler_rust/runtime/src/value/simd_int_ops.rs` (SSE2 `_mm_add_epi32`
    / `_mm_sub_epi32` for x4 add/sub; SSE4.1 `_mm_mullo_epi32` for x4 mul with
    wrapping-scalar fallback on plain SSE2; AVX2 `_mm256_{add,sub,mullo}_epi32`
    for x8; NEON `v{add,sub,mul}q_s32`). 6 dispatch arms + 6 wrapper fns
    added in interpreter_extern. Spec:
    `test/unit/lib/nogc_sync_mut/simd_int_arith_dispatch_spec.spl`.
    T1's chacha20 SIMD path can now use `simd_add_i32x4` directly (the
    `_vadd` simplification noted in the ChaCha20 update above is unblocked
    as a follow-up; chacha20.spl was not modified in this backfill pass).
  - Note: `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` has no `rt_simd_*`
    entries and was NOT updated for Phase 1; compiled-mode FFI marshalling for
    Vec4i/Vec8i is a follow-up. Interpreter mode is fully functional.
- **Date:** 2026-05-01
- **Status:** Proposed (Phase 1 landed; Phases 2–4 pending)
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
