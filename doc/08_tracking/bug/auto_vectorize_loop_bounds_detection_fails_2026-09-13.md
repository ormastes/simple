# `detect_loop_bounds_only` returns nil for `for i in 0..n` (5 specs RED)

- **Status:** RESOLVED 2026-09-13 — the defect was in the TEST FIXTURE, not in
  production code. Diagnosis below is retained because it was wrong in an
  instructive way.
- **Found:** 2026-09-13
- **Where:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl`
  (`detect_loop_bounds_only`), exercised by
  `test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl`

## Symptom

Five examples in `auto_vectorize_spec.spl` fail:

```
✗ for-i-in-0..n returns Some(LoopBounds)      expected false to equal true
✗ for-i-in-0..n lower bound is 0
✗ for-i-in-0..n step is 1
✗ for-i-in-0..n upper encodes local 30 as _l30
✗ for-i-in-0..arr.len upper encodes local 31 as _l31
```

`SPEC FILE VERDICT: ... executed=64 passed=59 failed=5`.

## Not caused by the AVX-512 widening

Found while landing `34b96e29837` (auto-vectorizer AVX-512 planning level).
Confirmed pre-existing by re-running the same spec with the widening disabled
(`auto_vectorize_x86_level(detect_capabilities(), false)`, forcing the old
`x86_64-v3` path): **identical** `executed=64 passed=59 failed=5`. The failures
are in dynamic loop-bounds detection, which does not read `chunk_width`.

## Impact

`detect_loop_bounds_only` failing on a dynamic upper bound means every
`for i in 0..n` loop reports an unknown trip count, so the rewriter's
divisibility and too-short guards see `trip_count = -1` and decline. Only
constant-bounded loops are reachable by the auto-vectorizer today. This caps
the real-world reach of auto-vectorization far more than the lane width did.

## Next step

Read the five expectations in `auto_vectorize_spec.spl` (they pin local-id
encoding `_l30`/`_l31`, so the defect may be in operand encoding rather than in
bounds detection itself) and bisect `detect_loop_bounds_only` against them.

## Environment note

Measured on Windows with `bin/simple.cmd run <spec>`; `bin/simple.cmd test`
cannot spawn its child on this host (`reason=child-died-early exit_code=-1`)
and reports `executed=0` for every spec, including untouched upstream ones.

## Resolution — the production code was correct all along

`MirOperandKind.Const` is `Const(value: MirConstValue, type_: MirType)`. The
fixture built it as:

```simple
fn make_const_op(val_text: text) -> MirOperand:
    MirOperand(kind: MirOperandKind.Const("i64", val_text))   # WRONG
```

— arguments in the wrong ORDER and of the wrong TYPES, left over from an older
signature. `operand_is_integer_one` then matched `Const(value, _)` against the
text `"i64"` instead of `MirConstValue.Int(1)`, returned false, and the
unit-step check never fired. Every *positive* `detect_bounds_from_block`
example failed while every *negative* one passed — which is exactly the
signature of a fixture that cannot construct the positive case, and is why the
"impact" section above (`for i in 0..n` unreachable) was wrong.

Fixed by splitting the helper into `make_int_const_op(v: i64)` and
`make_str_const_op(t: text)` with the correct variants
(`MirConstValue.Int` / `MirConstValue.Str`, `MirTypeKind.I64` /
`MirTypeKind.Opaque("str")`). `auto_vectorize_spec.spl` now passes **68/68**
(was 59/64; 4 of the new examples are the width-ladder guard added alongside).

Dynamic trip counts remain unsupported by the *rewriter* (guard R4), which is a
separate, documented limitation — but bounds DETECTION works, and always did.
