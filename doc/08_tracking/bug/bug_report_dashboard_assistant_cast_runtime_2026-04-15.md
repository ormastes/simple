# Dashboard Assistant Runtime Type Mismatch on Transcript Replay

## Summary

Initial report:

`bin/simple dashboard assistant` failed at runtime with:

```text
error: semantic: type mismatch: cannot convert string to int
```

This is **not** a generic bug in `n as i64` or `"{n as i64}"`.

Targeted control checks on 2026-04-15 showed both forms work in the current runtime:

- Plain numeric cast/interpolation:
  - `val n = 42.0`
  - `print(n as i64)` -> `42`
  - `print("{n as i64}")` -> `42`
- JSON-derived numeric cast/interpolation:
  - `json_parse("[42]")`
  - `json_array_get(..., 0)`
  - `val n = json_to_number(raw)`
  - `print(n as i64)` -> `42`
  - `print("{n as i64}")` -> `42`

So the bug is narrower:

- some assistant transcript/replay payload reaches an `as i64` or integer conversion path as a **string-backed runtime value**
- the assistant dashboard path assumes normalized numeric data but does not guard every mixed-shape input

## Reproduction

From the repo root:

```bash
bin/simple dashboard assistant
```

Observed result after the recent loader/import fixes:

```text
error: semantic: type mismatch: cannot convert string to int
```

## Scope Classification

### Not the bug

- generic `as i64` support
- generic string interpolation of casted numerics
- generic `json_to_number(...) as i64` for the simple `[42]` control case

### Likely bug surface

- assistant transcript normalization
- mixed JSON schema handling in `src/app/dashboard/assistant_collectors.spl`
- integer coercion from replay payload fields that are sometimes numeric and sometimes textual

## Most Suspicious Area

Current assistant collector helpers already need defensive coercion:

- `json_text_at(...)`
- `json_number_at(...)`

The remaining failure is likely in one of:

- a runtime cast on a value returned through nested transcript fields
- a helper downstream from transcript replay that still assumes numeric shape
- a path-specific field whose type differs across transcript producers

## Evidence

Working:

- `test/unit/compiler/interpreter/cast_numeric_parity_spec.spl`

Failing operational path:

- `bin/simple dashboard assistant`

Working operational path:

- `bin/simple dashboard status`

## Decision

Resolution status on 2026-04-15:

- `bin/simple dashboard assistant` now runs successfully against both the default workspace assistant store and an empty `HOME` fallback scenario.
- The root fixes were in the dashboard assistant collector/render path, not in language-level cast semantics.
- The generic `n as i64` and `"{n as i64}"` behavior remains valid and separately covered by interpreter regression tests.

Tracking note:

- The bug DB row was added through the managed writer path.
- Closing that row is currently blocked by a separate `bug-resolve` legacy-schema/runtime issue, so the DB status may still show `Open` until that utility is fixed.

Treat this as a **resolved dashboard assistant bug**, not as a language-level cast bug.

## Follow-up Plan

1. Capture one minimal failing assistant transcript fixture.
2. Reduce the failure to a direct collector-level repro.
3. Add a dedicated regression spec for that transcript shape.
4. Fix the specific coercion site instead of weakening numeric cast semantics globally.
