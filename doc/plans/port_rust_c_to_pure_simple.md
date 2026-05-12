# Plan: Port Rust/C Algorithms to Pure Simple + Optimize Compiler

## Status: Phases 1-2 DONE, Phases 3-5 REMAINING

---

## Phase 1: Fix Compiler Bugs — DONE

### 1A. Add `auto_vectorize` and `predicate_promote` to Pipelines — DONE
- `mod.spl` line 231: `"auto_vectorize"` in Speed pipeline
- `mod.spl` lines 250-251: `"auto_vectorize"` + `"predicate_promote"` in Aggressive pipeline
- Dispatch wired at lines 492-497

### 1B. Reconcile Crypto Symbol Names in rules_crypto.spl — DONE
- `cipher.spl`: `aes_round_software` (line 335), `aes_round_last_software` (341), `aes_inv_round_software` (346)
- `sha256_core.spl`: `compress_block` (85), `msg_schedule1` (88), `msg_schedule2` (91)
- `crc32.spl`: `update_byte`, `update_u32`, `update_u64` wrappers added
- `sha512.spl`: `sha512_round`, `sha512_msg_schedule_1/2` wrappers added
- `rules_crypto.spl`: added `SYM_CRYPTO_ROTR32` (line 62) and `SYM_CRYPTO_ROTL32` (line 63) matching `crypto.types.rotr32/rotl32`

### 1C. Make Crypto Code Use bitwise_utils Rotations — DONE (via 1B alternative)
- Instead of changing `types.spl`, added `rotr32`/`rotl32` as recognized symbols directly in `rules_crypto.spl` (lines 62-63, 93-94)
- Pattern engine now matches `crypto.types.rotr32`/`rotl32` directly

### 1D. Fix auto_vectorize Integer Type Detection — DONE
- `auto_vectorize.spl`: `has_integer_op` detection (line 340, 360), promotes `element_type_hint` to `"i32"` (line 396-397)
- Reduction path also detects integer ops (line 539: `red_elem_type`)
- K3 limitation documented at line 526 (hardcodes `"f32"` for that specific wave only)

---

## Phase 2: Remove FFI + Implement XXHash — DONE

### 2A. Remove FFI Externs from AES-128-GCM — DONE
- `aes128_gcm.spl`: all 6 `rt_aes_*` / `rt_tls13_*` externs removed, replaced with imports from `aes/sbox.spl`, `aes/cipher.spl`

### 2B. Implement XXHash in Pure Simple — DONE
- `src/os/crypto/xxhash.spl`: 300 lines, XXHash64 implementation with prime constants, 4 accumulator lanes, finalization

### 2C. Migrate SHA/DH/RSA FFI Callsites — DONE
- All crypto-specific `rt_aes_*`, `rt_tls13_*`, `rt_sha*_*`, `rt_dh_*`, `rt_rsa_*` externs removed
- Additional AES mode files cleaned: `aes256_gcm.spl`, `aes_modes.spl`, `aes256_ccm.spl`, `aes_gcm_siv.spl`, `aes_xts.spl`, `ocb3.spl`, `aes_cmac.spl`
- `pbkdf2.spl`: 4 PBKDF2 FFI externs removed

### 2C Note — Remaining `extern fn rt_` (non-crypto, OK to keep):
These are **runtime infrastructure** externs, not crypto FFI:
- `rt_bytes_u8_at` — byte array access (runtime primitive, used in whirlpool, aes_cmac, aria, camellia, ffdhe, sha224, sha384, sm3, snow3g_sr, zuc, ed25519, rsa_fallback)
- `rt_array_new_with_cap` — array allocation (runtime primitive, used in aes_cmac, aria, camellia)
- `rt_rdrand` / `rt_rndr` / `rt_riscv_seed` — hardware RNG instructions (cannot be pure Simple)
- `rt_time_now_unix_micros` — system clock (cannot be pure Simple)
- `rt_embedded_host_rsa_component` — embedded binary blob accessor (runtime infrastructure)
- `rt_black_box` — optimization barrier (runtime primitive)

---

## Phase 3: Compiler Optimization Enhancements — NOT STARTED

### 3A. Bounds-Check Elimination Pass — NOT STARTED
- **Create:** new pass in `src/compiler/60.mir_opt/mir_opt/`
- Detect array accesses in loops with monotonically increasing induction variable
- Hoist upper-bound check before loop, eliminate per-iteration checks
- Use existing `LoopInfo` from `loop_detect.spl` (has `trip_count: i64?`)
- **Impact:** VERY HIGH — deflate, SHA-256, all array-heavy code pay ~30-50% overhead
- Add to Speed and Aggressive pipelines in mod.spl

### 3B. @always_inline Attribute Support — NOT STARTED
- **File:** `src/compiler/60.mir_opt/mir_opt/inline.spl`
- No `always_inline` or `force_inline` support exists yet
- Extend annotation system to recognize `@always_inline`
- Modify `should_inline()` to return true for annotated functions regardless of size
- Annotate crypto primitives: `rotr32`, `shr32`, `add_mod32`, `sha256_ch`, `sha256_maj`
- **Impact:** HIGH — eliminates call overhead in tight crypto loops

### 3C. Feature Caps Cost Calibration — NOT STARTED
- **File:** `src/compiler/70.backend/feature_caps.spl`
- No `InstructionCost`, `latency`, or `throughput` fields exist yet
- Replace placeholder cost estimates with actual instruction latencies
- AES-NI: 1-cycle latency, SHA-NI: 3-4 cycles, PCLMULQDQ: 3 cycles
- **Impact:** Medium — correct cost model drives better intrinsic selection

### 3D. Loop Unrolling for Crypto — PARTIALLY DONE
- **File:** `src/compiler/60.mir_opt/mir_opt/loop_opt.spl`
- Partial unrolling (2x/4x) exists for loops ≤64 iterations (lines 103-107)
- `partial_unroll_loop` method implemented (line 168)
- **Remaining:** Verify threshold covers AES (10/12/14), SHA-256 (64), ChaCha20 (20)
- SHA-256's 64 rounds are at the boundary (`count <= 64`) — verify it actually fires

### 3E. GVN Enhancement for Crypto Mask Patterns — NOT STARTED
- **File:** `src/compiler/60.mir_opt/mir_opt/gvn.spl`
- No mask/identity/bitwidth logic exists yet (only commutativity "identity" in docstring)
- Recognize `x & 0xFFFFFFFF` as identity when x is known 32-bit
- Common in crypto `add_mod32` results — every add gets an unnecessary AND mask
- **Impact:** Medium — eliminates redundant masks throughout crypto code

---

## Phase 4: SIMD & Vectorization Completion — DONE

### 4A. Integer SIMD Lowering — DONE
- **File:** `src/compiler/60.mir_opt/mir_opt/simd_lowering.spl`
- Integer SIMD ops lowered: `xor_i32x4/x8`, `shl_i32x4/x8`, `shr_i32x4/x8` (lines 136-162)
- Enables ChaCha20 vectorized quarter-rounds

### 4B. AVX-512 Stub Completion — DONE
- **File:** `src/compiler/70.backend/backend/native/x86_64_avx512.spl`
- 31 `emit_*` functions implemented (was 9 stubs)
- Includes gather/scatter, k-mask ops, vpternlog, vpermd/vpermq, vbroadcast, vshuff, etc.

### 4C. SIMD Crypto Dispatch Table — DONE
- **File:** `src/runtime/runtime_simd_dispatch.h` + `runtime_simd_dispatch.c`
- `SimdCryptoDispatch` struct with 6 function pointers (aes_encrypt/decrypt, sha256_compress, chacha20_block, crc32_update, ghash_multiply)
- Scalar fallback stubs initialized; `simd_crypto_init()` placeholder for AES-NI/SHA-NI/PCLMULQDQ upgrade
- Feature detection: `simd_detect_aesni()`, `simd_detect_sha_ni()`, `simd_detect_pclmulqdq()`

---

## Phase 5: Library Hot-Path Optimization — NOT STARTED

### 5A. Deflate Batch Read — NOT STARTED
- `src/lib/common/compress/deflate.spl` exists
- Replace per-bit `_defl_read_bits` with batch 32-bit read

### 5B. SHA-256 Manual Unroll — NOT STARTED
- `src/lib/common/crypto/sha256_core.spl`: manually unroll 64-round loop by 4x

### 5C. ChaCha20 Direct SIMD Intrinsics — NOT STARTED
- `src/lib/common/crypto/chacha20.spl`: replace struct-field Vec4i with direct `simd_xor_i32x4` calls

### 5D. Zstd/LZ4 Multi-Byte Copy — NOT STARTED
- Replace per-byte loops with bulk copy intrinsics in compression libraries

---

## Summary

| Phase | Item | Status |
|-------|------|--------|
| 1A | Pipeline: auto_vectorize + predicate_promote | DONE |
| 1B | Symbol alignment: rules_crypto.spl + wrappers | DONE |
| 1C | Rotation matching via rules_crypto.spl | DONE |
| 1D | Integer type detection in auto_vectorize | DONE |
| 2A | AES-128-GCM FFI removal | DONE |
| 2B | XXHash pure Simple implementation | DONE |
| 2C | SHA/DH/RSA/AES-modes FFI migration | DONE |
| 3A | Bounds-check elimination pass | **NOT STARTED** |
| 3B | @always_inline attribute | **NOT STARTED** |
| 3C | Feature caps cost calibration | **NOT STARTED** |
| 3D | Loop unrolling for crypto | PARTIALLY DONE |
| 3E | GVN mask identity elimination | **NOT STARTED** |
| 4A | Integer SIMD lowering | DONE |
| 4B | AVX-512 stubs | DONE |
| 4C | SIMD crypto dispatch table | DONE |
| 5A | Deflate batch read | **NOT STARTED** |
| 5B | SHA-256 manual unroll | **NOT STARTED** |
| 5C | ChaCha20 SIMD intrinsics | **NOT STARTED** |
| 5D | Zstd/LZ4 multi-byte copy | **NOT STARTED** |

**Next:** Phase 3 — compiler optimization enhancements (3A bounds-check elim is highest impact).

---

## Critical Files (remaining work)

| File | Phase | Purpose |
|------|-------|---------|
| `src/compiler/60.mir_opt/mir_opt/` (new file) | 3A | Bounds-check elimination pass |
| `src/compiler/60.mir_opt/mir_opt/mod.spl` | 3A | Add bounds_check_elim to pipelines |
| `src/compiler/60.mir_opt/mir_opt/inline.spl` | 3B | @always_inline support |
| `src/compiler/70.backend/feature_caps.spl` | 3C | Cost calibration with real latencies |
| `src/compiler/60.mir_opt/mir_opt/loop_opt.spl` | 3D | Verify crypto loop thresholds |
| `src/compiler/60.mir_opt/mir_opt/gvn.spl` | 3E | Mask identity elimination |
| `src/lib/common/compress/deflate.spl` | 5A | Batch bit reads |
| `src/lib/common/crypto/sha256_core.spl` | 5B | Manual 4x unroll |
| `src/lib/common/crypto/chacha20.spl` | 5C | Direct SIMD intrinsics |
