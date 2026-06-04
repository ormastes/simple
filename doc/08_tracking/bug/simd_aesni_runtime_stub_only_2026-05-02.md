---
id: simd_aesni_runtime_stub_only_2026-05-02
status: RESOLVED
severity: low
discovered: 2026-05-02
discovered_by: K1 (Wave K AES SIMD wire-up agent — stalled mid-test)
updated: 2026-05-09
updated_by: Bug-fix agent (Cranelift AOT marshalling landed)
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

**Cranelift AOT registration (DONE):**
- `rt_simd_aes_round_u8x16` and `rt_simd_aes_round_last_u8x16` added to
  `RUNTIME_FUNCS` in `runtime_ffi.rs` as `&[I64, I64], &[I64]`.
- Flat-struct `extern "C"` wrappers in `simd_aes_ops.rs` use raw pointer
  arithmetic to unpack/repack Vec16u8 fields at byte offset `i * 8`,
  matching the layout produced by `compile_struct_init` (which uses
  `rt_alloc` + direct stores, NOT `rt_object_new`). The initial approach
  using `rt_object_field_get` was incorrect because `rt_alloc` does not
  write a HeapHeader, so `get_typed_ptr` would fail and return NIL.
- Old 33-arg lane-array ABI functions renamed to `_lanes` suffix (kept for
  seed/bootstrap parity).
- `tier_of()` now includes `name.starts_with("rt_simd_")` in the Ext tier.

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
running 5 tests
test value::simd_aes_ops::tests::fips197_round1_matches ... ok
test value::simd_aes_ops::tests::flat_struct_wrapper_fips197_round1 ... ok
test value::simd_aes_ops::tests::last_round_xors_key ... ok
test value::simd_aes_ops::tests::shift_rows_identity_on_zero ... ok
test value::simd_aes_ops::tests::shift_rows_known_vector ... ok
test result: ok. 5 passed; 0 failed; 0 ignored
```

## Resolution (2026-05-09)

All remaining items are now complete:

1. **Vec16u8 marshalling layer**: Flat-struct wrappers in `simd_aes_ops.rs`
   use raw pointer arithmetic (`rt_alloc` + `ptr.add(i * 8).write_unaligned`)
   to unpack/repack Vec16u8 struct fields, matching the codegen layout from
   `compile_struct_init`. The initial `rt_object_field_get` approach was
   wrong because `rt_alloc` produces flat memory without a `HeapHeader`,
   causing `get_typed_ptr(HeapObjectType::Object)` to fail silently.
2. **RUNTIME_FUNCS registration**: `rt_simd_aes_round_u8x16` and
   `rt_simd_aes_round_last_u8x16` added as `&[I64, I64], &[I64]`.
3. **tier_of() update**: `"rt_simd_"` prefix added to Ext tier block.
4. **RuntimeValue ABI fix**: Wrappers use `to_raw()`/`from_raw()` (bit-preserving)
   instead of `as_int()`/`from_int()` (which apply 3-bit tag shifting). In
   compiled mode, Cranelift passes raw `rt_alloc` pointers directly as i64
   vregs with NO tagging; `as_int()` would right-shift by 3 (corrupting the
   pointer) and `from_int()` would left-shift by 3 (corrupting the return).
5. **Test coverage**: `flat_struct_wrapper_fips197_round1` test exercises the
   actual extern symbol end-to-end against the FIPS 197 known-good vector,
   using `from_raw()`/`to_raw()` to match the real Cranelift calling convention.

The same flat-struct marshalling pattern can be applied to other `rt_simd_*`
externs (add_u8x16, CLMUL, Vec4i) as needed.

## Citations

- `src/compiler_rust/runtime/src/value/simd_aes_ops.rs` (full implementation)
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:966-972` (interpreter dispatch)
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:969-970` (dispatch routing)
- `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` (missing Cranelift registration)
- `src/lib/nogc_sync_mut/simd.spl:521-522` (extern declarations)
- `doc/01_research/cipher_simd_patterns_2026-05-02.md:1-148` (L5 corrections)
