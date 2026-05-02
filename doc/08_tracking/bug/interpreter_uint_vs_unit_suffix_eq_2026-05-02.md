# Interpreter `==` between `Value::UInt` and `Value::Unit{..., suffix}` returns false

**Filed:** 2026-05-02
**Status:** OPEN
**Severity:** medium (workaround available; obscures legitimate test assertions)
**Discovered by:** W8-8 during SIMD Phase 3 (Vec2u64 + PCLMUL) spec validation

## Summary

When a runtime extern handler returns `Value::UInt { value: u64, width: 64 }`
and a Simple test asserts equality against a u64-suffixed integer
literal (e.g. `0xdead_beef_cafe_babe_u64`), the equality compares
`Value::UInt(N)` against `Value::Unit { value: Box<Int(...)>, suffix: "u64", family: None }`
and returns false even when the underlying numeric values match.

## Repro

In `test/unit/lib/nogc_sync_mut/simd_clmul_spec.spl` (Phase 3 SIMD spec),
the following assertions failed:

```spl
val r = simd_clmul_lo_u64(vec_lo(0x7b_u64), vec_lo(0x48_u64))
expect r.lo == 0x1D18_u64
# expected 7448 to equal 7448_u64
```

```spl
val r = simd_xor_u64x2(...)
expect r.lo == 0xffff_ffff_ffff_ffff_u64
# expected 18446744073709551615 to equal -1_u64
```

```spl
val r = simd_xor_u64x2(...)
expect r.lo == 0xdead_beef_cafe_babe_u64
# expected 1311768467463790320 to equal 1311768467463790320_u64
```

The display format on the RHS shows `_u64` because the literal is
parsed into a `Value::Unit { value: Box<Int(...)>, suffix: "u64", family: None }`
wrapper, while my handler returns `Value::UInt { value, width: 64 }`.
Equality `UInt == Unit` falls through to the catch-all "not equal".

## Workaround (used in the Phase 3 spec)

Drop the `_u64` suffix from the assertion RHS and use the signed-int
two's-complement representation of the u64 bit pattern:

```spl
expect r.lo == 7448             # was: == 0x1D18_u64
expect r.lo == -1                # was: == 0xffff_ffff_ffff_ffff_u64
expect r.lo == -2401053089206453570  # was: == 0xdead_beef_cafe_babe_u64
```

This compares `UInt(N)` against `Int(N as i64)` which the equality op
DOES handle. It is a coverup workaround per `feedback_no_coverups.md`
that should be replaced once this bug is fixed.

## Suspected Fix Locations

- `src/compiler_rust/compiler/src/interpreter/operators.rs` (or wherever
  `==` dispatch lives): the equality op should unwrap `Value::Unit { value, .. }`
  on either side before comparing the inner numeric value, OR treat
  `UInt(N) == Unit{Int(N')}` as equal whenever `N as i64 == N'`.

- Alternative: extend `Value::UInt` to carry an optional unit-suffix tag
  and compare across the two representations. This is a bigger change.

The minimal fix is the unwrap-on-Unit approach since callers expect
suffix tags to be metadata, not equality-affecting.

## Cross-Links

- Phase 3 spec: `test/unit/lib/nogc_sync_mut/simd_clmul_spec.spl` (3 of
  15 cases use the workaround; the other 12 use unsuffixed numeric
  literals naturally).
- Handler: `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`
  `pack_vec2u64` returns `Value::UInt { value, width: 64 }` for u64 lanes.
- Related: `feedback_no_coverups.md` (W8-8 chose to ship the workaround
  because the underlying bug is out of Phase 3 scope; this doc tracks
  the proper fix).
