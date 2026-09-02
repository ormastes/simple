# Every `Vec16u8`-taking SIMD extern is uncallable from the interpreter

- **Status:** OPEN
- **Found:** 2026-09-02, while wiring dual-run pairs for
  `src/runtime/runtime_simd_dispatch.c`
- **Severity:** blocks all interpreter-side use and all dual-run coverage of the
  u8x16 SIMD family (AES round, byte add/xor, PSHUFB shuffle)

## Symptom

Calling any `Vec16u8` extern from Simple under the tree-walk interpreter
(`bin/simple test` / `bin/simple run`) fails before either side computes
anything:

```
runtime: rt_simd_shuffle_u8x16(a): field u0 must be an integer, got UInt { value: 1, width: 8 }
```

Measured 2026-09-02 with `bin/simple.exe` (md5 `d52d770724a9f8797e98ac7819709ab9`)
on a spec that built its operands with the stdlib constructor
`Vec16u8.from_array(...)`.

## Root cause

Two halves of the same contract disagree about the lane representation.

- `src/lib/nogc_sync_mut/simd_crypto.spl` declares `struct Vec16u8` with
  sixteen fields typed **`u8`**. The interpreter represents a `u8` field as
  `Value::UInt { value, width: 8 }`.
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:1204`
  (`require_u8_field`, reached from `unpack_vec16u8` at `:1227`) matches
  **only** `Some(Value::Int(n))` and errors on every other variant.

So the type the stdlib publishes for these externs is precisely the type the
bridge refuses. There is no way to construct an acceptable `Vec16u8` through
the public constructors (`from_array`, `splat`, `zero`) — all of them produce
`u8`-typed fields.

Contrast `Vec4i64` (`src/lib/nogc_sync_mut/simd.spl:634`), whose fields are
`i64`: `rt_simd_add_i64x4` / `rt_simd_sub_i64x4` work fine, and are dual-run
covered in `test/01_unit/lib/common/spec/dual_run_simd_lane_spec.spl`.

## Blast radius

Every extern whose signature mentions `Vec16u8`, all declared in
`src/lib/nogc_sync_mut/simd_crypto.spl`: `rt_simd_shuffle_u8x16`,
`rt_simd_add_u8x16`, `rt_simd_xor_u8x16`, `rt_simd_aes_round_u8x16`,
`rt_simd_aes_round_last_u8x16`. The C implementations in
`src/runtime/runtime_simd_dispatch.c` are not at fault and are presumably
reachable from the native/JIT path; only the interpreter bridge is broken.

## Fix

Widen `require_u8_field` to accept `Value::UInt { value, width }` (range-check
`value <= 255` exactly as the `Value::Int` arm range-checks `0..=255`), keeping
the `Value::Int` arm for compatibility. The sibling helpers
`require_u32_value` / `require_u64_value` already accept both variants, which
is why the `[u32]` engine2d span externs work — this is a one-helper
divergence, not a design decision.

This is Rust seed code, so the fix needs a seed rebuild before it can be
observed.

## Unblock condition

Once fixed, wire the already-written scalar twin
`std.common.simd_lane_pure.shuffle_u8x16_pure` as a `@dual_pair` against
`rt_simd_shuffle_u8x16`. The reference and its intended case set (identity
mask, reversal, cross-vector indices 16..31, bit-7 zeroing, out-of-window
indices 32..47 that must fold through the 5-bit mask, all-zero operands,
`a == b`) are ready; only the oracle is unreachable.

**Deliberately not worked around.** An adapter struct with `i64` fields would
make a dual-run harness certify a code path no real caller uses — the same
reasoning that left `rt_base64url_encode` unwired in
`test/01_unit/lib/common/spec/dual_run_tranche_b_spec.spl`.

## Cross-platform note

Observed on Windows. The defect is in platform-independent Rust
(`match` on a `Value` variant) with no `cfg` guards anywhere on the path, so it
is expected to reproduce identically on Linux and macOS — but that was **not**
tested from this host, and the claim should be verified before it is relied on.
