---
id: simd_aesni_runtime_stub_only_2026-05-02
status: MOSTLY-RESOLVED
severity: low
discovered: 2026-05-02
discovered_by: K1 (Wave K AES SIMD wire-up agent — stalled mid-test)
updated: 2026-05-09
updated_by: Bug-fix agent (context-resumed session)
related: doc/01_research/cipher_simd_patterns_2026-05-02.md (J2 + L5 corrections)
related: doc/08_tracking/bug/bug_simd_bulk_copy_blocked_by_spl_array_layout_2026-05-02.md (K2)
---

# AES-NI / Vec16u8 round-op externs: interpreter-wired, Cranelift-blocked

## Status Update (2026-05-09)

The original bug title ("stub declarations only") was **factually wrong** at time
of filing. The runtime implementations exist and are fully functional with
hardware acceleration on x86_64 (AES-NI) and AArch64 (NEON Crypto Extensions),
plus scalar fallback on all other platforms. FIPS 197 test vectors pass (4/4).

The remaining gap is **Cranelift compiled-mode (AOT) linkage only**. Interpreter
mode works correctly today.

## Original Summary (corrected)

`src/lib/nogc_sync_mut/simd.spl:521-522` declares:

```
extern fn rt_simd_aes_round_u8x16(state: Vec16u8, key: Vec16u8) -> Vec16u8
extern fn rt_simd_aes_round_last_u8x16(state: Vec16u8, key: Vec16u8) -> Vec16u8
```

K1 claimed "no runtime backing" — this was wrong. Phase 3 shipped full
implementations.

## Infrastructure Checklist

### 1. AES-NI runtime impl (x86) -- DONE

`src/compiler_rust/runtime/src/value/simd_aes_ops.rs:199-221`
- `aes_round_x86()` at line 199: uses `_mm_aesenc_si128`
- `aes_round_last_x86()` at line 211: uses `_mm_aesenclast_si128`
- Runtime feature detection: `is_x86_feature_detected!("aes")` at line 153

### 2. ARMv8 Crypto Extensions impl -- DONE

`src/compiler_rust/runtime/src/value/simd_aes_ops.rs:223-251`
- Uses `vaeseq_u8` + `vaesmcq_u8` for AES round
- Uses `vaeseq_u8` (without MC) for last round
- Conditional compilation via `cfg(target_arch = "aarch64")`

### 3. Capability detection -- DONE

`src/compiler_rust/runtime/src/value/simd_aes_ops.rs:153-161`
- x86_64: `is_x86_feature_detected!("aes")` runtime check (CPUID bit 25 ECX)
- AArch64: compile-time `cfg(target_feature = "aes")` (standard for AArch64)
- Fallback: scalar FIPS 197 implementation at lines 169-197

### 4. Runtime registration -- PARTIALLY DONE

**Interpreter dispatch (DONE):**
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:969-970`
  Routes `"rt_simd_aes_round_u8x16"` and `"rt_simd_aes_round_last_u8x16"`
  to the simd module.
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:966-972`
  Unpacks Vec16u8 Value::Object fields, calls `aes_round_u8x16` /
  `aes_round_last_u8x16`, repacks result.

**Cranelift AOT registration (NOT DONE -- remaining blocker):**
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` has ZERO `rt_simd_*`
  entries (confirmed by grep). All existing entries use boxed `I64`
  RuntimeValue ABI.
- The `extern "C"` functions in `simd_aes_ops.rs:260-354` use a 33-arg
  lane-array ABI (32 individual u8 lanes + `*mut u8` output pointer).
- The `.spl` declares `(Vec16u8, Vec16u8) -> Vec16u8` (struct ABI).
- **Registering in runtime_ffi.rs requires a Vec16u8 marshalling layer in
  the Cranelift codegen** that decomposes struct fields to individual lane
  args and reconstructs the result from the output pointer. This layer
  does not exist for any `rt_simd_*` function.
- The `tier_of()` function (line 36) routes `rt_vec_*` to Ext tier but has
  no `rt_simd_*` prefix match -- would need adding alongside the FFI entries.

### 5. Scalar fallback -- DONE

`src/compiler_rust/runtime/src/value/simd_aes_ops.rs:169-197`
- Full FIPS 197 scalar implementation: ShiftRows + SubBytes + MixColumns + XOR
- Automatically selected on platforms without AES-NI / NEON Crypto

### 6. Update J2 audit doc -- DONE (by L5)

`doc/01_research/cipher_simd_patterns_2026-05-02.md` lines 1-148 contain
L5 corrections filed 2026-05-02 that accurately recategorize all SIMD externs
as INTERPRETER-WIRED / CRANELIFT-BLOCKED.

## Test Evidence

```
$ cd src/compiler_rust && cargo test -p simple-runtime simd_aes_ops
running 4 tests
test value::simd_aes_ops::tests::fips197_round1_matches ... ok
test value::simd_aes_ops::tests::last_round_xors_key ... ok
test value::simd_aes_ops::tests::shift_rows_identity_on_zero ... ok
test value::simd_aes_ops::tests::shift_rows_known_vector ... ok
test result: ok. 4 passed; 0 failed; 0 ignored
```

## Remaining Work

The ONLY remaining item is Cranelift AOT compiled-mode support, which requires:

1. A Vec16u8 marshalling layer in the Cranelift codegen that maps between the
   `.spl` struct-level `(Vec16u8, Vec16u8) -> Vec16u8` signature and the
   `extern "C"` 33-arg lane-array ABI.
2. Adding `rt_simd_aes_round_u8x16` and `rt_simd_aes_round_last_u8x16` to
   `RUNTIME_FUNCS` in `runtime_ffi.rs` with the correct lane-decomposed
   parameter types.
3. Adding `"rt_simd_"` prefix to `tier_of()` Ext tier (line 36).

This is the same class of blocker as K2 (zstd bulk-copy SIMD) and affects ALL
`rt_simd_*` externs uniformly, not just AES. It should be addressed as a single
infrastructure task covering the Vec16u8/Vec4i/Vec2u64 marshalling layer.

## Proposed Fix

**Bundle with Vec16u8 marshalling infrastructure.** When the Cranelift codegen
gains a struct-to-lane decomposition pass for SIMD types, all `rt_simd_*`
externs (AES, CLMUL, Vec4i ops, etc.) can be registered in `runtime_ffi.rs`
in one sweep. This is not AES-specific work.

## Citations

- `src/compiler_rust/runtime/src/value/simd_aes_ops.rs` (full implementation)
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:966-972` (interpreter dispatch)
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:969-970` (dispatch routing)
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` (missing Cranelift registration)
- `src/lib/nogc_sync_mut/simd.spl:521-522` (extern declarations)
- `doc/01_research/cipher_simd_patterns_2026-05-02.md:1-148` (L5 corrections)
