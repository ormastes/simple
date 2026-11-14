# u64 shift/display go SIGNED outside a `-> u64` typed function

- **Status:** OPEN
- **Found:** 2026-09-03, while writing dual-run tranche E twins for
  `rt_simd_shl_u64x4` / `rt_simd_shr_u64x4`
- **Area:** language / tree-walk interpreter, u64 type propagation
- **Engine:** `bin/simple test` (tree-walk interpreter), Rust seed
  `v1.0.0-rc.1`, Windows x86_64
- **Not a duplicate of** `u64_decimal_literal_parsed_through_i64_stage4_2026-08-02.md`
  or `parser_decimal_u64_rejected_as_i64_2026_08_04.md`: those are the parser
  *rejecting* a large decimal literal. Here the literal is accepted and then
  evaluated **silently as signed** — no diagnostic at all.

## Symptom

Two distinct signed leaks, both measured directly:

```
val big: u64 = 18446744073709551615
print(big.to_string())        # prints "-1"     -- expected 18446744073709551615
print((big << 1).to_string()) # prints "-2"     -- expected 18446744073709551614
print((big >> 1).to_string()) # prints "-1"     -- expected 9223372036854775807
```

The same operands routed through a function with a **declared `-> u64` return
type** are correct:

```
fn shl_lane(x: u64, s: i32) -> u64:
    return x << s
fn shr_lane(x: u64, s: i32) -> u64:
    return x >> s

print(shl_lane(big, 1).to_string())   # 18446744073709551614  correct
print(shr_lane(big, 1).to_string())   # 9223372036854775807   correct (LOGICAL shift)
```

So the u64-ness is carried by the declared return type, not by the `val`
annotation on the binding. `>>` is a logical shift when the value is genuinely
u64 and an arithmetic shift when it has leaked to i64 — the difference between
`9223372036854775807` and `-1`.

## Why it matters

The runtime oracle is unambiguous: `rt_simd_shr_u64x4` on an all-ones lane
answers `9223372036854775807`. A pure-Simple twin written the obvious way
(`val` bindings, no typed wrapper) would answer `-1` and diverge against the C
lane — the twin would look wrong when the language, not the twin, is wrong.

## Workaround currently in the tree (do not silently normalize this)

`src/lib/common/simd_lane_pure.spl` implements the twins as `-> u64` typed
functions `shl_u64_pure` / `shr_u64_pure`, and the spec
`test/01_unit/lib/common/spec/dual_run_tranche_e_spec.spl` routes every
comparison through a `fn u64_text(x: u64) -> text` helper so `.to_string()` is
always evaluated in a u64-typed context. Both carry a load-bearing comment
pointing here. That is a workaround, not a fix: the underlying `val`/inference
path is still wrong and still silent.

## Reproduction

Any spec file containing the first block above under
`bin/simple test <spec>`. No SIMD, extern or FFI involvement is needed — the
`rt_simd_*` oracles are only how it was noticed.

## Suggested fix direction

Propagate the declared `u64` type of a `val` binding into the binding's value
and into arithmetic/shift/`to_string` on it, the same way a declared `-> u64`
return type already does. A diagnostic on the silent i64 demotion would be an
acceptable interim, since the current failure mode is a wrong answer with no
signal.

## Triage 2026-11-13 (P3 tools lane)
No code change this lane. Verified the record's analysis still describes the
fix surface accurately: the u64-ness is carried by declared `-> u64` return
types, not by `val` annotations, so the defect lives in the compiler
frontend/interpreter type-propagation path (src/compiler + interpreter,
outside this lane's bounded src/app|src/lib .spl scope). The in-tree
workaround (`src/lib/common/simd_lane_pure.spl` typed wrappers +
`fn u64_text` in the tranche-E spec) remains the standing mitigation; a
diagnostic on silent i64 demotion would be an acceptable interim per the
record. Routed to the compiler lane.

## Addendum 2026-11-14 — lane p3-batch-b: no longer reproduces (verified fixed)

Seed: Rust seed built from `release/1.0.0` @ `bb2a83ed4da4` on Linux aarch64
(md5 prefix `1f3d1c3645ed`). The record's exact repro now prints
`18446744073709551615` / `18446744073709551614` / `9223372036854775807` under
both `run` and `test` (interpreter). Pinned by
`test/01_unit/bugs/u64_val_binding_unsigned_spec.spl` (6/6), with negative
vectors: an `i64` binding still displays `-1` and keeps an arithmetic `>>`, and
the `-> u64` typed-fn route is unchanged. Not re-measured on Windows x86_64,
where the record was filed. The `u64_text` helper in
`dual_run_tranche_e_spec.spl` is left in place: it also covers u64 array
elements and extern-returned struct fields, which this spec does not pin.
