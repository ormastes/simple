# JIT array out-of-bounds read leaks the raw `RT_NIL` sentinel (`3`) instead of `nil`/panic

- **Filed:** 2026-08-07
- **Severity:** P2 — wrong text output, no crash, no error; not a value-corruption
  defect on the scale of the sibling below, but silently wrong
- **Status:** OPEN
- **Affects:** JIT/native lane only. Both `xs.get(i)` (Option MISS, printed
  without `??`) and bare `xs[i]` (out-of-bounds index) on the same receiver.
- **Found while re-verifying:** `doc/08_tracking/bug/list_get_returns_tag_boxed_value_shifted_left_3_2026-07-28.md`
  (that doc's `<<3` hit-path shift defect is fixed; this is a separate,
  narrower miss-path finding made during that re-verification, split out here
  per the "file it, don't bury it in a closed doc" rule).

## Symptom

```simple
fn main():
    val xs = [10, 20, 30]
    print("miss={xs.get(9)}\n")          # JIT: miss=3   (interpreter: miss=nil)
    print("val={xs[9]}\n")                # JIT: val=3    (rc=0, no panic)
```

`3` is `RT_NIL`, the runtime's flat-Option/OOB sentinel word (see
`dict_get_preserve_flat_nil` and the `emit_const_int(3)` none-arm in
`method_calls_literals.spl`'s `lower_array_first_or_last`, both in
`src/compiler/50.mir/_MirLoweringExpr/`). When the result is consumed through
`??` it is correctly recognized as absent (`xs.get(9) ?? -1` → `-1` on both
engines). When it is interpolated directly into text (no unwrap operator), the
JIT prints the raw sentinel value instead of formatting it as `nil`/`None`,
while the tree-walk interpreter formats it correctly.

## Which engine

| expr | JIT (default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| `xs.get(9)` interpolated bare | `3` — WRONG | `nil` — correct |
| `xs.get(9) ?? -1` | `-1` — correct | `-1` — correct |
| `xs[9]` (bare OOB index, no `.get`) | `3` — WRONG, rc=0, no panic | not re-checked |

Confirmed via `cranelift_jit::backend` log lines that the JIT run was real
(not a silent interpreter fallback). Binary: seed at
`bin/release/x86_64-unknown-linux-gnu/simple` (prints the "bootstrap seed
only" banner); pure-Simple self-hosted lane not re-checked this session (no
bootstrap rebuild performed).

## Root cause (not yet investigated)

Likely: the value's `to_text`/interpolation formatting path decodes/dispatches
on the *declared* element type (e.g. `i64`) without first checking the
Option-nil-sentinel guard that `dict_get_preserve_flat_nil` and the
`Array.first()/.last()` none-arm apply before handing a value to the general
decode/format machinery. Needs someone to trace the interpolation lowering
for a bare Option-typed operand (not wrapped in `??`, `.unwrap()`, or a
`match`) and check whether it takes the same nil-guard branch those call
sites do.

## Not chased further here

Out of scope for the re-verification task that found it; filed so it isn't
lost, not fixed.
