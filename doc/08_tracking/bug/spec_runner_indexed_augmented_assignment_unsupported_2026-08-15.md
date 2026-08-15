# Spec runner rejects indexed augmented assignment that `run` accepts

- **Date:** 2026-08-15
- **Status:** OPEN
- **Area:** interpreter / test runner semantic analysis
- **Symptom:** `semantic: invalid assignment: unsupported augmented assignment target`

## Summary

Under `bin/simple test` (spec runner), any augmented assignment whose target
is an INDEXED lvalue fails at execution time with
`semantic: invalid assignment: unsupported augmented assignment target`:

- `arr[i] += v` (local array, variable index) — FAILS
- `self.field[i] += v` (class array field, inside a `me` method) — FAILS
- `self.field += v` (plain field) — works
- `x += v` (plain var) — works

The exact same code executes correctly under `bin/simple run` (verified with
the Rust seed binary). So this is a spec-runner-only semantic gap, not a
general interpreter limitation.

## Repro

Minimal failing spec (run with `bin/simple test <file> --no-cache`):

```
use std.spec

class P:
    a: [i64]
    me bump(i: i64):
        self.a[i] += 1

fn local_indexed(i: i64) -> i64:
    var a: [i64] = [0, 0]
    a[i] += 7
    a[i]

describe "aug probe":
    it "field-indexed augassign in method":       # FAILS
        val p = P(a: [0, 0])
        p.bump(1)
        expect(p.a[1]).to_equal(1)
    it "local array indexed augassign in fn":     # FAILS
        expect(local_indexed(1)).to_equal(7)
```

Both `it` blocks fail with the semantic error above; rewriting to
`a[i] = a[i] + 1` passes. The same class/function executed via
`bin/simple run` prints the correct results.

## Real-world impact

`src/lib/common/ui/render_opt/damage_tiles.spl` and `damage_plan.spl` use
this construct in library code, which makes parts of them uncallable from any
spec:

- `DirtyTilePyramid.mark_rect` — `self.dirty_len[level] += 1` (damage_tiles.spl:126)
- `damage_tiles_mark_property_damage` with non-empty damage (calls mark_rect)
- `build_damage_plan` vertical run merge — `rects[rect_index + 3] += h` (damage_plan.spl:135)

`test/01_unit/lib/ui/render_opt/damage_plan_branch_coverage_spec.spl` carries
an EXCLUSION comment referencing this bug and works around it by writing
`tile_epoch` slots directly instead of calling `mark_rect`; the excluded
branches are the unreachable coverage remainder there (damage_plan 17/19,
damage_tiles 15/16 decisions).

## Fix direction

The spec-runner execution path's assignment lowering should desugar
`target[i] op= v` to `target[i] = target[i] op v` (or support the indexed
lvalue directly), matching the `run` path's behavior.
