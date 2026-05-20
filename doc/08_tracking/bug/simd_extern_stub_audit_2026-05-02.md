# Bug / Audit: SIMD Extern Stub Survey — simd.spl
# 2026-05-02  (Wave L / L5)
# **Updated 2026-05-20 (status check)** — no new stubs since Wave 15; 60 wired, 0 stub, open gaps unchanged.

**Status:** OPEN (ongoing tracker) — all extern declarations in simd.spl are
now wired; remaining open items are the str_* orphan gap (§3.2, interpreter-internal),
the uniform Cranelift gap (§4), and the missing-feature additions from Wave 15 (now done).

**Purpose:** Provide a complete, cited map of every `extern fn rt_simd_*`
declared in `src/lib/nogc_sync_mut/simd.spl` and its actual wiring status, so
that future agents do not repeat the K1 error of assuming a runtime
implementation is absent when only the wrong file was grepped.

---

## §1  Method

### 1.1  What counts as "wired"

An extern is **INTERPRETER-WIRED** if ALL of the following are true:

1. `extern fn rt_simd_*` declaration exists in `simd.spl`.
2. A matching dispatch arm exists in
   `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`.
3. A `pub fn rt_simd_*` implementation exists in
   `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`.
4. A backing implementation exists — either:
   - (a) a `pub fn` in `src/compiler_rust/runtime/src/value/simd_*.rs`
         (the Rust runtime crate, potentially using hardware intrinsics), OR
   - (b) a scalar element-wise implementation inline in `interpreter_extern/simd.rs`
         (no hardware intrinsic; correct but no SIMD speedup on any ISA).

Category (a) backing uses platform SIMD intrinsics on x86_64 and aarch64 where
available, with scalar fallback for other targets.  Category (b) is always
scalar.  Both are distinguished in §2.

An extern is **FULLY STUB** if conditions 2, 3, and 4 are all absent.

**Critical note on Cranelift:** `src/compiler_rust/compiler/src/codegen/
runtime_ffi.rs` lines 261-294 contain only `rt_vec_*` generic-vector entries.
There are ZERO `rt_simd_*` entries.  This means ALL rt_simd_* externs —
whether interpreter-wired or stub — are **CRANELIFT-BLOCKED**: calling them
from code compiled to native via Cranelift AOT will fail with a
missing-symbol error.  The "interpreter-wired / Cranelift-blocked" split is
uniform; it is not a property of individual externs.

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
# Phase 2: add/xor/aes_round/aes_round_last wired. Phase 4: shuffle_u8x16 wired
# (scalar fallback). PCLMUL wired (Phase 3). simd_xor_u8x16 available.
```

Updated 2026-05-19 (Wave 15): comment rewritten to reflect current state.
`shuffle_u8x16` and Vec4u64 ops are now wired (scalar fallback, Phase 4).
PCLMUL/CLMUL is wired (§2.A.6).

---

## §2  INTERPRETER-WIRED Externs (51 total as of 2026-05-19)

Split into §2.A (hardware-backed — real intrinsics in runtime crate) and
§2.B (scalar-only — correct but no SIMD speedup on any ISA).

All 51 are simultaneously CRANELIFT-BLOCKED (see §4).

---

### §2.A  Hardware-Backed (runtime crate intrinsics)

These use real SIMD intrinsics on x86_64 (SSE2/AES-NI/PCLMULQDQ) and
aarch64 (NEON/AES/PMULL), with scalar fallback for other targets.

#### §2.A.1  Capability detection (7 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_has_sse` | 30 | 1022 |
| `rt_simd_has_avx` | 31 | 1019 |
| `rt_simd_has_avx2` | 32 | 1018 |
| `rt_simd_has_neon` | 33 | 1020 |
| `rt_simd_has_rvv` | 34 | 1021 |
| `rt_simd_detect_profile` | 35 | 1008 |
| `rt_simd_profile_name` | 36 | 1030 |

Runtime: `interpreter_extern/simd.rs:90-120`.

#### §2.A.2  Vec4i — i32×4 integer ops (8 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_i32x4` | 350 | 999 |
| `rt_simd_sub_i32x4` | 351 | 1041 |
| `rt_simd_mul_i32x4` | 352 | 1026 |
| `rt_simd_xor_i32x4` | 353 | 1046 |
| `rt_simd_and_i32x4` | 354 | 1004 |
| `rt_simd_or_i32x4` | 355 | 1028 |
| `rt_simd_shl_i32x4` | 356 | 1031 |
| `rt_simd_shr_i32x4` | 357 | 1033 |

Runtime: `interpreter_extern/simd.rs:793-821`.  These primitives are used by
SHA-256 `sha256_little_sigma0_x4` and are available for ChaCha20/Salsa20.

#### §2.A.3  Vec8i — i32×8 integer ops (8 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_add_i32x8` | 395 | 1000 |
| `rt_simd_sub_i32x8` | 396 | 1042 |
| `rt_simd_mul_i32x8` | 397 | 1027 |
| `rt_simd_xor_i32x8` | 398 | 1047 |
| `rt_simd_and_i32x8` | 399 | 1005 |
| `rt_simd_or_i32x8` | 400 | 1029 |
| `rt_simd_shl_i32x8` | 401 | 1032 |
| `rt_simd_shr_i32x8` | 402 | 1034 |

Runtime: `interpreter_extern/simd.rs:825-853`.

#### §2.A.4  Vec16u8 — u8×16 byte ops (4 externs)

| Extern | simd.spl | mod.rs | Runtime file |
|--------|----------|--------|--------------|
| `rt_simd_add_u8x16` | 509 | 1001 | `simd_byte_ops.rs` — SSE2 `_mm_add_epi8` / NEON `vaddq_u8` |
| `rt_simd_xor_u8x16` | 661 | 1049 | `simd_byte_ops.rs` — SSE2 `_mm_xor_si128` / NEON `veorq_u8` |
| `rt_simd_aes_round_u8x16` | 521 | 1003 | `simd_aes_ops.rs:240+` — AES-NI `_mm_aesenc_si128` / ARM `vaeseq_u8`+`vaesmcq_u8` |
| `rt_simd_aes_round_last_u8x16` | 522 | 1002 | `simd_aes_ops.rs:240+` — AES-NI `_mm_aesenclast_si128` / ARM final round |

Note: K1's claim of "no runtime backing" for AES round ops was wrong.

#### §2.A.5  Vec2u64 — u64×2 scalar ops (3 externs)

| Extern | simd.spl | mod.rs |
|--------|----------|--------|
| `rt_simd_vec2u64_new` | 588 | 1045 |
| `rt_simd_vec2u64_lo` | 589 | 1044 |
| `rt_simd_vec2u64_hi` | 590 | 1043 |

Runtime: `interpreter_extern/simd.rs:1112+`.

#### §2.A.6  Vec2u64 — CLMUL / XOR ops (3 externs)

| Extern | simd.spl | mod.rs | Runtime |
|--------|----------|--------|---------|
| `rt_simd_clmul_lo_u64` | 592 | 1007 | `simd_clmul_ops.rs` — PCLMULQDQ `_mm_clmulepi64_si128` / ARM `vmull_p64` |
| `rt_simd_clmul_hi_u64` | 593 | 1006 | same |
| `rt_simd_xor_u64x2` | 594 | 1048 | `simd_clmul_ops.rs` |

J2 §3.3, §6.4, §M P5 stated PCLMULQDQ was "not yet exposed as a Simple extern"
and cited simd.spl:446 as authority.  That comment was stale.  These externs
have been present and wired since Phase 3.

---

### §2.B  Scalar-Only (no hardware intrinsics; lane-wise Rust arithmetic)

These live entirely in `interpreter_extern/simd.rs` — there is no
`simd_float_ops.rs` or similar in the runtime value crate.  They are correct
and callable from interpreter mode, but provide no SIMD speedup on any target.

#### §2.B.1  Vec4f — f32×4 float ops (6 externs)

| Extern | simd.spl | mod.rs | simd.rs |
|--------|----------|--------|---------|
| `rt_simd_add_f32x4` | 260 | 996 | 857 |
| `rt_simd_sub_f32x4` | 261 | 1038 | 861 |
| `rt_simd_mul_f32x4` | 262 | 1023 | 865 |
| `rt_simd_div_f32x4` | 263 | 1009 | 869 |
| `rt_simd_fma_f32x4` | 264 | 1012 | 873 |
| `rt_simd_hadd_f32x4` | 780 | 1015 | 921 (**NEW 2026-05-19**) |

#### §2.B.2  Vec4f horizontal reduction ops (2 externs — NEW 2026-05-19)

| Extern | simd.spl | mod.rs | simd.rs |
|--------|----------|--------|---------|
| `rt_simd_hmax_f32x4` | 781 | 1016 | 930 |
| `rt_simd_hmin_f32x4` | 782 | 1017 | 940 |

These were the last externs declared in simd.spl that lacked interpreter wiring.
Implementation: scalar reduction over `unpack_vec4f` array.

#### §2.B.3  Vec8f — f32×8 float ops (5 externs)

| Extern | simd.spl | mod.rs | simd.rs |
|--------|----------|--------|---------|
| `rt_simd_add_f32x8` | 290 | 997 | 877 |
| `rt_simd_sub_f32x8` | 291 | 1039 | 881 |
| `rt_simd_mul_f32x8` | 292 | 1024 | 885 |
| `rt_simd_div_f32x8` | 293 | 1010 | 889 |
| `rt_simd_fma_f32x8` | 294 | 1013 | 893 |

#### §2.B.4  Vec4d — f64×4 double ops (5 externs)

| Extern | simd.spl | mod.rs | simd.rs |
|--------|----------|--------|---------|
| `rt_simd_add_f64x4` | 320 | 998 | 897 |
| `rt_simd_sub_f64x4` | 321 | 1040 | 901 |
| `rt_simd_mul_f64x4` | 322 | 1025 | 905 |
| `rt_simd_div_f64x4` | 323 | 1011 | 909 |
| `rt_simd_fma_f64x4` | 324 | 1014 | 913 |

---

## §3  Gaps

### §3.1  Fully Stub Externs in simd.spl (0 as of 2026-05-19)

All externs declared in simd.spl are now interpreter-wired.  The 2026-05-10
snapshot listed 18 fully stub externs; they have since been implemented
(float ops) or are covered by the 2026-05-19 hadd/hmax/hmin additions.

### §3.2  Orphan ops — impl-only, no extern decl in simd.spl

These three have `pub fn` implementations in `simd.rs` and dispatch arms in
`mod.rs`, but have **no `extern fn` declaration in `simd.spl`**.  They cannot
be called from user Simple code.  They appear to be used by the interpreter
string subsystem internally.

| Name | simd.rs | mod.rs | simd.spl |
|------|---------|--------|----------|
| `rt_simd_str_search` | 1320 | 1037 | **ABSENT** |
| `rt_simd_str_last_index_of` | 1337 | 1036 | **ABSENT** |
| `rt_simd_str_equal` | 1354 | 1035 | **ABSENT** |

**Action required (future wave):** Decide whether to:
- Expose as Simple externs: add `extern fn` declarations to simd.spl, or
- Mark as interpreter-internal: add a comment in mod.rs noting they are not
  callable from Simple code (the dispatch entry is harmless but misleading).

### §3.3  Missing features (not declared in simd.spl)

| Feature | Status |
|---------|--------|
| `rt_simd_shuffle_u8x16` | **DONE 2026-05-19 Wave 15** — declared in simd.spl, scalar impl in simd.rs, wired in mod.rs |
| `Vec4u64` struct + u64×4 arithmetic ops | **DONE 2026-05-19 Wave 15** — Vec4u64 struct declared in simd.spl; `xor/and/or/shl/shr_u64x4` + `vec4u64_new/get` declared and wired (scalar fallback) |

---

## §4  Half-Wired: Interpreter-Wired but Cranelift-Blocked (all 51 from §2)

Every extern listed in §2 works in interpreter mode but fails in Cranelift
AOT compiled mode (`--mode=native`).

Root cause: `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` lines
261-294 contain only `rt_vec_*` entries; there are no `rt_simd_*` entries.

**To unblock Cranelift for a specific extern**, the following three edits are
needed per extern:

1. Add a `SigRef` entry in `runtime_ffi.rs` (the Cranelift signature table).
2. Add a `call_rt_simd_*` helper in the codegen layer analogous to existing
   `call_rt_vec_*` helpers.
3. Emit the call from the relevant Simple AST lowering pass.

This is MEDIUM-effort Rust-seed work.  The runtime implementations already
exist for all 51 interpreter-wired ops; only the Cranelift codegen wiring is
missing.

---

## §5  Implications for Cipher Work

### §5.1  Immediately landable in interpreter / SMF mode

| Task | Required externs | Status |
|------|-----------------|--------|
| Wire AES common/aes/ to SIMD round | `rt_simd_aes_round_u8x16`, `rt_simd_aes_round_last_u8x16`, `rt_simd_xor_u8x16` | ALL wired (hardware) |
| Add pure-Simple ChaCha20 | `rt_simd_{add,sub,xor,shl,shr,or}_i32x4` | ALL wired (hardware) |
| Add pure-Simple Salsa20 SIMD path | Same Vec4i set | ALL wired (hardware) |
| SHA-256 schedule add_i32x4 | `rt_simd_add_i32x4` | Wired (hardware) |
| SHA-512 schedule 2-wide u64 | `rt_simd_vec2u64_new/lo/hi`, `rt_simd_xor_u64x2` | ALL wired (hardware) |
| Poly1305 via CLMUL | `rt_simd_clmul_lo/hi_u64`, `rt_simd_xor_u64x2` | ALL wired (hardware) |
| ML/signal float ops (Vec4f/Vec8f/Vec4d) | All 15 float externs | ALL wired (scalar only — no HW speedup) |
| Vec4f reduction | `rt_simd_{hadd,hmax,hmin}_f32x4` | ALL wired (scalar only — NEW 2026-05-19) |

### §5.2  Previously blocked — now unblocked (Wave 15)

| Task | Blocker | Resolution |
|------|---------|------------|
| AES ShiftRows via shuffle | `rt_simd_shuffle_u8x16` absent from simd.spl | **DONE** — wired (scalar fallback) |
| SHA-3 / Keccak | `Vec4u64` + `rt_simd_{xor,and,or,shl,shr}_u64x4` absent | **DONE** — Vec4u64 declared + all 5 ops wired (scalar fallback) |
| SHA-512 4-wide u64 | Same Vec4u64 absence | **DONE** — same Vec4u64 fix unblocks this |

### §5.3  Blocked until Cranelift runtime_ffi.rs is updated

Any task that must run in Cranelift AOT compiled mode (`--mode=native`) requires
adding `rt_simd_*` entries to `runtime_ffi.rs`.  This applies uniformly to all
51 interpreter-wired externs.  Until then, all SIMD cipher code must remain
in interpreter / SMF mode or use the scalar FFI path for compiled deployments.

### §5.4  J2 recommendation re-evaluation (updated 2026-05-19)

| J2 Recommendation | 2026-05-19 Assessment |
|-------------------|-----------------------|
| Rec 1: Wire AES with existing SIMD round primitive | DONE — all AES round + xor_u8x16 wired with hardware intrinsics |
| Rec 2: Add pure-Simple ChaCha20 with Vec4i | UNBLOCKED — all Vec4i ops wired, no new externs needed |
| Rec 3: Add Vec4u64 integer intrinsics | DONE (Wave 15) — Vec4u64 + xor/and/or/shl/shr_u64x4 wired (scalar fallback); SHA-3/Keccak unblocked |

---

## §6  Change Log

| Date | Change |
|------|--------|
| 2026-05-02 | Initial audit (Wave L/L5): 32 wired, 18 stub |
| 2026-05-10 | `rt_simd_xor_u8x16` wired through full stack (runtime + interpreter + simd.spl extern decl); Vec16u8 count becomes 4 |
| 2026-05-19 | Full re-audit: float ops (15) reclassified as interpreter-wired scalar fallback (previously miscategorised as stub); `rt_simd_hadd/hmax/hmin_f32x4` implemented in `interpreter_extern/simd.rs:921-950` and wired in mod.rs:1015-1017; str_* orphan gap documented (§3.2); total wired count = 51, stub = 0; condition 4 of §1.1 definition expanded to include scalar-only impls; line-number tables re-verified against post-edit source |
| 2026-05-19 (Wave 15) | §3.3 gaps closed: `rt_simd_shuffle_u8x16` (scalar PSHUFB impl) + `Vec4u64` struct + `rt_simd_{xor,and,or,shl,shr}_u64x4` + `rt_simd_vec4u64_{new,get}` all declared in simd.spl and wired in interpreter_extern/simd.rs + mod.rs; total wired count = 60; §5.2 blockers resolved; Rec 3 (J2) complete |
| 2026-05-20 | Status check: grep confirms 60 wired, 0 stub — no new extern declarations added since Wave 15. Open items unchanged: str_* orphan gap (§3.2, interpreter-internal only), uniform Cranelift gap (§4, all 60 externs absent from runtime_ffi.rs). No doc update to wiring tables required. |

---

*End of document.*

*All file:line citations verified against actual source as of 2026-05-19 post-edit.*
