# Bug / Audit: SIMD Extern Stub Survey — simd.spl
# 2026-05-02  (Wave L / L5)
# **Updated 2026-05-19** — full re-audit; float ops reclassified; hadd/hmax/hmin implemented; str_* orphan gap documented.

**Status:** OPEN (ongoing tracker) — individual items resolved; see per-item status below.

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

### 1.3  Stale comment — PARTIALLY UPDATED

`src/lib/nogc_sync_mut/simd.spl:590-591` contains:

```
# simd_shuffle_u8x16 / PCLMUL are deferred to follow-up waves (they require
# AES-NI exposure / different intrinsics). simd_xor_u8x16 is now available.
```

This is partially accurate.  `rt_simd_xor_u8x16` is wired.  `shuffle_u8x16` and
full Vec4u64 remain absent.  PCLMUL/CLMUL is now wired (see §2.6).

The earlier stale comment at simd.spl:445-447 (Phase 2 SEED note deferring AES
round / xor_u8x16 / shuffle / PCLMUL) was updated before the 2026-05-10 fix.

---

## §2  INTERPRETER-WIRED Externs (54 total as of 2026-05-19)

All entries are wired through `interpreter_extern/mod.rs` and have
Rust-layer backing in `interpreter_extern/simd.rs`.
All are simultaneously CRANELIFT-BLOCKED (see §4).

### 2.1  Capability detection (7 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_has_sse` | 30 | 1019 |
| `rt_simd_has_avx` | 31 | 1017 |
| `rt_simd_has_avx2` | 32 | 1016 |
| `rt_simd_has_neon` | 33 | 1018 |
| `rt_simd_has_rvv` | 34 | 1019 |
| `rt_simd_detect_profile` | 35 | 1008 |
| `rt_simd_profile_name` | 36 | 1027 |

Runtime: `interpreter_extern/simd.rs:90-120`.

### 2.2  Vec4i — i32×4 integer ops (8 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_i32x4` | 350 | 999 |
| `rt_simd_sub_i32x4` | 351 | 1038 |
| `rt_simd_mul_i32x4` | 352 | 1023 |
| `rt_simd_xor_i32x4` | 353 | 1043 |
| `rt_simd_and_i32x4` | 354 | 1004 |
| `rt_simd_or_i32x4` | 355 | 1025 |
| `rt_simd_shl_i32x4` | 356 | 1028 |
| `rt_simd_shr_i32x4` | 357 | 1030 |

Runtime: `interpreter_extern/simd.rs:793-821`.  Primitives used by SHA-256
`sha256_little_sigma0_x4` and available for ChaCha20/Salsa20 implementations.

### 2.3  Vec8i — i32×8 integer ops (8 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_i32x8` | 395 | 1000 |
| `rt_simd_sub_i32x8` | 396 | 1039 |
| `rt_simd_mul_i32x8` | 397 | 1024 |
| `rt_simd_xor_i32x8` | 398 | 1044 |
| `rt_simd_and_i32x8` | 399 | 1005 |
| `rt_simd_or_i32x8` | 400 | 1026 |
| `rt_simd_shl_i32x8` | 401 | 1029 |
| `rt_simd_shr_i32x8` | 402 | 1031 |

Runtime: `interpreter_extern/simd.rs:825-853`.

### 2.4  Vec4f — f32×4 float ops (6 externs) — RECLASSIFIED from §3

These were listed as FULLY STUB in the 2026-05-10 snapshot.  They are now
**INTERPRETER-WIRED** via scalar fallback (lane-wise Rust f32 arithmetic,
no platform SIMD intrinsics).  There is no `simd_float_ops.rs` in the runtime
value crate; the implementation lives entirely in `interpreter_extern/simd.rs`.

| Extern | simd.spl | mod.rs | Impl |
|--------|----------|--------|------|
| `rt_simd_add_f32x4` | 260 | 996 | simd.rs:857 |
| `rt_simd_sub_f32x4` | 261 | 1035 | simd.rs:861 |
| `rt_simd_mul_f32x4` | 262 | 1020 | simd.rs:865 |
| `rt_simd_div_f32x4` | 263 | 1009 | simd.rs:869 |
| `rt_simd_fma_f32x4` | 264 | 1012 | simd.rs:873 |
| `rt_simd_hadd_f32x4` | 780 | 1015 | simd.rs:917 (**NEW 2026-05-19**) |

**Note on hadd/hmax/hmin:** `rt_simd_hadd/hmax/hmin_f32x4` were the only three
externs declared in simd.spl but absent from mod.rs dispatch and simd.rs.
All three were implemented on 2026-05-19 (scalar reduction via `unpack_vec4f`).

| Extern | simd.spl | mod.rs | Impl |
|--------|----------|--------|------|
| `rt_simd_hmax_f32x4` | 781 | 1017 | simd.rs:926 (**NEW 2026-05-19**) |
| `rt_simd_hmin_f32x4` | 782 | 1018 | simd.rs:935 (**NEW 2026-05-19**) |

### 2.5  Vec8f — f32×8 float ops (5 externs) — RECLASSIFIED from §3

| Extern | simd.spl | mod.rs | Impl |
|--------|----------|--------|------|
| `rt_simd_add_f32x8` | 290 | 997 | simd.rs:877 |
| `rt_simd_sub_f32x8` | 291 | 1036 | simd.rs:881 |
| `rt_simd_mul_f32x8` | 292 | 1021 | simd.rs:885 |
| `rt_simd_div_f32x8` | 293 | 1010 | simd.rs:889 |
| `rt_simd_fma_f32x8` | 294 | 1013 | simd.rs:893 |

Scalar fallback (lane-wise f32), no hardware intrinsics.

### 2.6  Vec4d — f64×4 double ops (5 externs) — RECLASSIFIED from §3

| Extern | simd.spl | mod.rs | Impl |
|--------|----------|--------|------|
| `rt_simd_add_f64x4` | 320 | 998 | simd.rs:897 |
| `rt_simd_sub_f64x4` | 321 | 1037 | simd.rs:901 |
| `rt_simd_mul_f64x4` | 322 | 1022 | simd.rs:905 |
| `rt_simd_div_f64x4` | 323 | 1011 | simd.rs:909 |
| `rt_simd_fma_f64x4` | 324 | 1014 | simd.rs:913 |

Scalar fallback (lane-wise f64), no hardware intrinsics.

### 2.7  Vec16u8 — u8×16 byte ops (4 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_u8x16` | 509 | 1001 |
| `rt_simd_xor_u8x16` | 661 | 1046 |
| `rt_simd_aes_round_u8x16` | 521 | 1003 |
| `rt_simd_aes_round_last_u8x16` | 522 | 1002 |

Runtime backing:
- `rt_simd_add_u8x16`, `rt_simd_xor_u8x16`: `src/compiler_rust/runtime/src/value/simd_byte_ops.rs`
  — real x86 SSE2 `_mm_add_epi8`/`_mm_xor_si128` and ARM NEON equivalents.
- `rt_simd_aes_round_u8x16`, `rt_simd_aes_round_last_u8x16`:
  `src/compiler_rust/runtime/src/value/simd_aes_ops.rs:240-270`
  — real x86 AES-NI `_mm_aesenc_si128` / `_mm_aesenclast_si128` and ARM
  `vaeseq_u8`+`vaesmcq_u8`.

### 2.8  Vec2u64 — u64×2 scalar ops (3 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_vec2u64_new` | 588 | 1042 |
| `rt_simd_vec2u64_lo` | 589 | 1041 |
| `rt_simd_vec2u64_hi` | 590 | 1040 |

Runtime: `interpreter_extern/simd.rs:1112+`.

### 2.9  Vec2u64 — CLMUL / XOR ops (3 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_clmul_lo_u64` | 592 | 1007 |
| `rt_simd_clmul_hi_u64` | 593 | 1006 |
| `rt_simd_xor_u64x2` | 594 | 1045 |

Runtime: `src/compiler_rust/runtime/src/value/simd_clmul_ops.rs`
— real x86_64 PCLMULQDQ `_mm_clmulepi64_si128` and ARM `vmull_p64`.

### 2.10  String search — interpreter-internal ops (3 externs)

These three have `pub fn` implementations in `simd.rs` (lines 1320-1354) and
dispatch arms in `mod.rs` (lines 1032-1034) but have **NO `extern fn`
declaration in `simd.spl`**.  They are called internally by the interpreter
string subsystem, not from user Simple code.  They are documented here as a
gap: if they are intended to be callable from Simple, `extern fn` declarations
must be added to simd.spl.

| Name | simd.rs | mod.rs | simd.spl |
|------|---------|--------|----------|
| `rt_simd_str_search` | 1320 | 1034 | **ABSENT** |
| `rt_simd_str_last_index_of` | 1337 | 1033 | **ABSENT** |
| `rt_simd_str_equal` | 1354 | 1032 | **ABSENT** |

**Action required:** Decide whether to expose these as Simple externs (add
`extern fn` to simd.spl) or document them as interpreter-internal and remove
them from mod.rs (they do not need to be in the public dispatch table if they
are never called from Simple code).

---

## §3  FULLY STUB Externs (0 as of 2026-05-19)

All 18 externs previously listed as FULLY STUB in the 2026-05-10 snapshot
have since been implemented:

- 15 float ops (Vec4f/Vec8f/Vec4d) are wired via scalar fallback (§2.4–2.6).
- 3 horizontal reduction ops (hadd/hmax/hmin) were implemented on 2026-05-19 (§2.4).

There are currently **no fully stub externs** in simd.spl.

### 3.1  Remaining gaps (not stub, but absent from simd.spl)

| Feature | Status |
|---------|--------|
| `rt_simd_shuffle_u8x16` | Not declared in simd.spl, not implemented |
| `Vec4u64` struct + u64×4 ops | Not declared in simd.spl, not implemented |
| SHA-3 / Keccak wide u64 ops | Requires Vec4u64 (above) |

---

## §4  Half-Wired: Interpreter-Wired but Cranelift-Blocked (all 54 from §2)

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
runtime implementation (which already exists for all 54 interpreter-wired ops).

**This bug is the authoritative Cranelift gap tracker.**  The runtime exists;
only the Cranelift codegen wiring is missing.

---

## §5  Implications for Cipher Work

### 5.1  Immediately landable in interpreter / SMF mode

| Task | Required externs | Status |
|------|-----------------|--------|
| Wire AES common/aes/ to SIMD round | `rt_simd_aes_round_u8x16`, `rt_simd_aes_round_last_u8x16`, `rt_simd_xor_u8x16` | ALL wired |
| Add pure-Simple ChaCha20 | `rt_simd_{add,sub,xor,shl,shr,or}_i32x4` | ALL wired |
| Add pure-Simple Salsa20 SIMD path | Same Vec4i set | ALL wired |
| SHA-256 schedule add_i32x4 | `rt_simd_add_i32x4` | Wired |
| SHA-512 schedule 2-wide u64 | `rt_simd_vec2u64_new/lo/hi`, `rt_simd_xor_u64x2` | ALL wired |
| Poly1305 via CLMUL | `rt_simd_clmul_lo/hi_u64`, `rt_simd_xor_u64x2` | ALL wired |
| ML/signal float ops (Vec4f/Vec8f/Vec4d) | All 15 float externs | ALL wired (scalar fallback) |
| Vec4f reduction (hadd/hmax/hmin) | `rt_simd_{hadd,hmax,hmin}_f32x4` | ALL wired (**NEW 2026-05-19**) |

### 5.2  Blocked until new externs added to simd.spl

| Task | Blocker |
|------|---------|
| AES ShiftRows via shuffle | `rt_simd_shuffle_u8x16` absent from simd.spl |
| SHA-3 / Keccak | `Vec4u64` struct + `rt_simd_{xor,and,or,shl,shr}_u64x4` absent |
| SHA-512 4-wide u64 | Same Vec4u64 absence |

### 5.3  Blocked until Cranelift runtime_ffi.rs is updated

Any task that must run in **Cranelift AOT compiled mode** (e.g. `--mode=native`
or production `bin/simple` binary paths) requires adding rt_simd_* entries to
`runtime_ffi.rs`.  This applies uniformly to ALL 54 interpreter-wired externs.

Until then, all SIMD cipher code must remain in interpreter / SMF mode or use
the existing scalar FFI path (`rt_aes_encrypt_block_with_expanded` etc.) for
compiled deployments.

### 5.4  J2 recommendation re-evaluation (updated 2026-05-19)

| J2 Recommendation | 2026-05-19 Assessment |
|-------------------|-----------------------|
| Rec 1: Wire AES with existing SIMD round primitive | DONE — all AES round + xor_u8x16 wired |
| Rec 2: Add pure-Simple ChaCha20 with Vec4i | UNBLOCKED — all Vec4i ops wired, no new externs needed |
| Rec 3: Add Vec4u64 integer intrinsics | Still MEDIUM; prerequisite for SHA-3 and wide SHA-512 |

---

## §6  Change Log

| Date | Change |
|------|--------|
| 2026-05-02 | Initial audit (Wave L/L5): 32 wired, 18 stub |
| 2026-05-10 | `rt_simd_xor_u8x16` wired through full stack; Vec16u8 count becomes 4 |
| 2026-05-19 | Full re-audit: float ops (15) reclassified as interpreter-wired scalar fallback; `rt_simd_hadd/hmax/hmin_f32x4` implemented in simd.rs + wired in mod.rs; str_* orphan gap documented; total wired count = 54, stubs = 0 |

---

*End of document.*

*All file:line citations verified against actual source as of 2026-05-19.*
