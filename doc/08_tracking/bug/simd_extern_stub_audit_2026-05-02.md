# Bug / Audit: SIMD Extern Stub Survey — simd.spl
# 2026-05-02  (Wave L / L5)

**Purpose:** Provide a complete, cited map of every `extern fn rt_simd_*`
declared in `src/lib/nogc_sync_mut/simd.spl` and its actual wiring status, so
that future agents do not repeat the K1 error of assuming a runtime
implementation is absent when only the wrong file was grepped.

---

## §1  Method

### 1.1  What counts as "wired"

An extern is **INTERPRETER-WIRED** if ALL of the following are true:

1. `extern fn rt_simd_*` declaration exists in `simd.spl`.
2. A matching `"rt_simd_*" => simd::rt_simd_*(&evaluated)` arm exists in
   `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.
3. A `pub fn rt_simd_*` implementation exists in
   `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`.
4. At least one runtime backing function exists in
   `src/compiler_rust/runtime/src/value/` (the Rust runtime crate).

An extern is **FULLY STUB** if conditions 2, 3, and 4 are all absent.

**Critical note on Cranelift:** `src/compiler_rust/compiler/src/codegen/
runtime_ffi.rs` is the Cranelift FFI signature table.  Lines 261-294 contain
only `rt_vec_*` generic-vector entries.  There are ZERO `rt_simd_*` entries.
This means ALL rt_simd_* externs — whether interpreter-wired or stub —
are **CRANELIFT-BLOCKED**: calling them from code compiled to native via
Cranelift AOT will fail with a missing-symbol error.

The "interpreter-wired / Cranelift-blocked" split is uniform.  It is not a
property of individual externs; it is a gap in runtime_ffi.rs.

### 1.2  Grep patterns used

```
# Step 1 — extern declarations
grep -n "extern fn rt_simd_" src/lib/nogc_sync_mut/simd.spl

# Step 2 — interpreter dispatch
grep -n "rt_simd_" src/compiler_rust/compiler/src/interpreter_extern/mod.rs

# Step 3 — interpreter implementations
grep -n "pub fn rt_simd_" src/compiler_rust/compiler/src/interpreter_extern/simd.rs

# Step 4 — runtime implementations (Rust crate, NOT src/runtime C)
grep -rn "rt_simd_\|aes_round\|clmul\|add_u8x16" \
  src/compiler_rust/runtime/src/value/

# Step 5 — Cranelift FFI table
grep -n "rt_simd_\|rt_vec_" \
  src/compiler_rust/compiler/src/codegen/runtime_ffi.rs
```

K1 bug doc `simd_aesni_runtime_stub_only_2026-05-02.md` searched
`interpreter_extern/ffi_array.rs` and `src/runtime/` (the C runtime).
Both are wrong files.  The correct dispatch table is `interpreter_extern/mod.rs`
and the correct Rust runtime is `src/compiler_rust/runtime/src/value/`.

### 1.3  Stale comment

`src/lib/nogc_sync_mut/simd.spl:445-447` contains:

```
# Phase 2 SEED: Vec16u8 is a type carrier + add op only.
# AES round / xor_u8x16 / shuffle / PCLMUL deferred to follow-up.
```

This comment is STALE.  AES round ops and CLMUL ops shipped in Phase 3 and are
fully interpreter-wired.  The comment has not been updated.

---

## §2  INTERPRETER-WIRED Externs (32 total)

All 32 entries are wired through `interpreter_extern/mod.rs:835-899` and have
Rust runtime backing.  All 32 are simultaneously CRANELIFT-BLOCKED.

### 2.1  Capability detection (7 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_has_sse` | 30 | 835 |
| `rt_simd_has_avx` | 31 | 836 |
| `rt_simd_has_avx2` | 32 | 837 |
| `rt_simd_has_neon` | 33 | 838 |
| `rt_simd_has_rvv` | 34 | 839 |
| `rt_simd_detect_profile` | 35 | 840 |
| `rt_simd_profile_name` | 36 | 841 |

Runtime: `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:62-92`.

### 2.2  Vec4i — i32×4 integer ops (8 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_i32x4` | 350 | 863 |
| `rt_simd_sub_i32x4` | 351 | 864 |
| `rt_simd_mul_i32x4` | 352 | 865 |
| `rt_simd_xor_i32x4` | 353 | 866 |
| `rt_simd_and_i32x4` | 354 | 867 |
| `rt_simd_or_i32x4` | 355 | 868 |
| `rt_simd_shl_i32x4` | 356 | 869 |
| `rt_simd_shr_i32x4` | 357 | 870 |

Runtime: `interpreter_extern/simd.rs:538-575`.  These are the primitives
used by SHA-256 `sha256_little_sigma0_x4` (sha256.spl:100-115) and available
for ChaCha20/Salsa20 implementations.

### 2.3  Vec8i — i32×8 integer ops (8 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_i32x8` | 395 | 871 |
| `rt_simd_sub_i32x8` | 396 | 872 |
| `rt_simd_mul_i32x8` | 397 | 873 |
| `rt_simd_xor_i32x8` | 398 | 874 |
| `rt_simd_and_i32x8` | 399 | 875 |
| `rt_simd_or_i32x8` | 400 | 876 |
| `rt_simd_shl_i32x8` | 401 | 877 |
| `rt_simd_shr_i32x8` | 402 | 878 |

Runtime: `interpreter_extern/simd.rs:577-614`.

### 2.4  Vec16u8 — u8×16 byte ops (3 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_u8x16` | 509 | 883 |
| `rt_simd_aes_round_u8x16` | 521 | 888 |
| `rt_simd_aes_round_last_u8x16` | 522 | 889 |

Runtime backing:
- `rt_simd_add_u8x16`: `src/compiler_rust/runtime/src/value/simd_byte_ops.rs`
  — real x86 SSE2 `_mm_add_epi8` and ARM NEON `vaddq_u8`.
- `rt_simd_aes_round_u8x16`, `rt_simd_aes_round_last_u8x16`:
  `src/compiler_rust/runtime/src/value/simd_aes_ops.rs:240-270`
  — real x86 AES-NI `_mm_aesenc_si128` / `_mm_aesenclast_si128` and ARM
  `vaeseq_u8`+`vaesmcq_u8`.  K1's claim of "no runtime backing" was wrong.

### 2.5  Vec2u64 — u64×2 scalar ops (3 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_vec2u64_new` | 588 | 894 |
| `rt_simd_vec2u64_lo` | 589 | 895 |
| `rt_simd_vec2u64_hi` | 590 | 896 |

Runtime: `interpreter_extern/simd.rs:768-790`.  J2 §8.4 claimed Vec2u64 was
absent — this is incorrect.

### 2.6  Vec2u64 — CLMUL / XOR ops (3 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_clmul_lo_u64` | 592 | 897 |
| `rt_simd_clmul_hi_u64` | 593 | 898 |
| `rt_simd_xor_u64x2` | 594 | 899 |

Runtime: `src/compiler_rust/runtime/src/value/simd_clmul_ops.rs`
— real x86_64 PCLMULQDQ `_mm_clmulepi64_si128` and ARM `vmull_p64`.

J2 §3.3, §6.4, and §M P5 all stated PCLMULQDQ was "not yet exposed as a
Simple extern" and cited simd.spl:446 as authority.  That comment is stale.
These externs have been present and interpreter-wired since Phase 3.

---

## §3  FULLY STUB Externs (18 total)

These externs are declared in simd.spl but have no entry in
`interpreter_extern/mod.rs`, no implementation in `interpreter_extern/simd.rs`,
and no backing in the Rust runtime value crate.  Calling them from interpreted
Simple code will produce a runtime dispatch error.

### 3.1  Vec4f — f32×4 float ops (5 externs)

| Extern | simd.spl |
|--------|----------|
| `rt_simd_add_f32x4` | 260 |
| `rt_simd_sub_f32x4` | 261 |
| `rt_simd_mul_f32x4` | 262 |
| `rt_simd_div_f32x4` | 263 |
| `rt_simd_fma_f32x4` | 264 |

### 3.2  Vec8f — f32×8 float ops (5 externs)

| Extern | simd.spl |
|--------|----------|
| `rt_simd_add_f32x8` | 290 |
| `rt_simd_sub_f32x8` | 291 |
| `rt_simd_mul_f32x8` | 292 |
| `rt_simd_div_f32x8` | 293 |
| `rt_simd_fma_f32x8` | 294 |

### 3.3  Vec4d — f64×4 double ops (5 externs)

| Extern | simd.spl |
|--------|----------|
| `rt_simd_add_f64x4` | 320 |
| `rt_simd_sub_f64x4` | 321 |
| `rt_simd_mul_f64x4` | 322 |
| `rt_simd_div_f64x4` | 323 |
| `rt_simd_fma_f64x4` | 324 |

### 3.4  Vec4f horizontal reduction ops (3 externs)

| Extern | simd.spl |
|--------|----------|
| `rt_simd_hadd_f32x4` | 628 |
| `rt_simd_hmax_f32x4` | 629 |
| `rt_simd_hmin_f32x4` | 630 |

---

## §4  Half-Wired: Interpreter-Wired but Cranelift-Blocked (all 32 from §2)

Every extern listed in §2 is simultaneously "half-wired": it works in
interpreter mode but fails in Cranelift AOT compiled mode.

The root cause is a single omission in one file:
`src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` lines 261-294
contain only `rt_vec_*` entries.  There are no `rt_simd_*` entries.

**To unblock Cranelift for a specific extern**, the following three edits are
needed per extern:

1. Add a `SigRef` entry in `runtime_ffi.rs` (the Cranelift signature table).
2. Add a `call_rt_simd_*` helper in the codegen layer analogous to existing
   `call_rt_vec_*` helpers.
3. Emit the call from the relevant Simple AST lowering pass.

This is a MEDIUM-effort Rust-seed change; it does not require touching the
runtime implementation (which already exists for the 32 interpreter-wired ops).

**This bug is the authoritative Cranelift gap tracker.**  It supersedes K1's
framing of "Rust-seed unblocker needed" — the runtime exists; only the
Cranelift codegen wiring is missing.

---

## §5  Implications for Cipher Work

### 5.1  Immediately landable in interpreter / SMF mode

The following cipher tasks can proceed today using only interpreter-mode
execution (no Cranelift AOT required):

| Task | Required externs | Status |
|------|-----------------|--------|
| Wire AES common/aes/ to SIMD round | `rt_simd_aes_round_u8x16`, `rt_simd_aes_round_last_u8x16` + new `rt_simd_xor_u8x16` | AES round wired; XOR extern absent from simd.spl entirely (must add) |
| Add pure-Simple ChaCha20 | `rt_simd_{add,sub,xor,shl,shr,or}_i32x4` | ALL wired (mod.rs:863-870) |
| Add pure-Simple Salsa20 SIMD path | Same Vec4i set | ALL wired |
| SHA-256 schedule add_i32x4 | `rt_simd_add_i32x4` | Wired (mod.rs:863) |
| SHA-512 schedule 2-wide u64 | `rt_simd_vec2u64_new/lo/hi`, `rt_simd_xor_u64x2` | ALL wired (mod.rs:894-899) |
| Poly1305 via CLMUL | `rt_simd_clmul_lo/hi_u64`, `rt_simd_xor_u64x2` | ALL wired (mod.rs:897-899) |

### 5.2  Blocked until new externs added to simd.spl

| Task | Blocker |
|------|---------|
| AES AddRoundKey / CTR XOR | `rt_simd_xor_u8x16` declaration absent from simd.spl; must add extern + interpreter/simd.rs impl + mod.rs arm |
| AES ShiftRows via shuffle | `rt_simd_shuffle_u8x16` absent from simd.spl |
| SHA-3 / Keccak | `Vec4u64` struct + `rt_simd_{xor,and,or,shl,shr}_u64x4` absent from simd.spl |
| SHA-512 4-wide u64 | Same Vec4u64 absence |
| Float SIMD (ML, signal processing) | All Vec4f/Vec8f/Vec4d externs are fully stub (§3) |

### 5.3  Blocked until Cranelift runtime_ffi.rs is updated

Any task that must run in **Cranelift AOT compiled mode** (e.g. `--mode=native`
or production `bin/simple` binary paths) requires adding rt_simd_* entries to
`runtime_ffi.rs`.  This applies uniformly to ALL 32 interpreter-wired externs.

Until then, all SIMD cipher code must remain in interpreter / SMF mode or use
the existing scalar FFI path (`rt_aes_encrypt_block_with_expanded` etc.) for
compiled deployments.

### 5.4  J2 recommendation re-evaluation

| J2 Recommendation | L5 Assessment |
|-------------------|---------------|
| Rec 1: Wire AES with existing SIMD round primitive | Reconfirmed as top priority; difficulty TRIVIAL-interpreter. "No new externs needed" was wrong — `rt_simd_xor_u8x16` must be added. |
| Rec 2: Add pure-Simple ChaCha20 with Vec4i | Reconfirmed TRIVIAL-interpreter (J2 rated MEDIUM; all Vec4i ops wired, no new externs). |
| Rec 3: Add Vec4u64 integer intrinsics | Still MEDIUM; prerequisite for SHA-3 and wide SHA-512. Unchanged. |

---

*End of document.*

*Generated by Wave L / L5 stub audit, 2026-05-02.*
*All file:line citations verified against actual source; no fabricated locations.*
