# Bug: `simple test` daemon evaluator diverges from `simple run` on `text?`-returning lookup + equality pattern

**Status:** OPEN — workaround applied in new code, latent defect left in place in existing code per scope constraint (see below)

**Date:** 2026-07-20
**Reporter:** DRAWIR-PATCH lane (draw_ir_patch.spl / draw_ir_diff.spl id-map slice)
**Severity:** Correctness (silent false result under `simple test`, only at moderate array scale ~20-30 elements; not reproducible under `simple run`)
**Related:** `doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md` item 7 (DrawIR patch)

---

## Summary

A helper function of the shape "loop over a collection, return the first
matching value as a nilable (`T?`), then compare it with `== nil` / `!=` at
the call site" produces a **different result under the `simple test` daemon
evaluator than under `simple run`**, for collections around ~20-30 elements.
Both evaluators agree at small scale (2-5 elements), which is why this went
unnoticed in existing coverage.

## Reproduction (found, then fixed in NEW code)

While building `src/lib/common/ui/draw_ir_patch.spl`, `draw_ir_patch_commands_equal`
(which flattens two `DrawIrComposition`s and compares commands field-by-field)
called a style-change helper of this shape:

```
fn _draw_ir_patch_style_value(command: DrawIrCommand, key: text) -> text?:
    for prop in command.computed_style:
        if prop.key == key:
            return prop.value
    nil

fn _draw_ir_patch_style_changed(a: DrawIrCommand, b: DrawIrCommand) -> bool:
    if a.computed_style.len() != b.computed_style.len():
        return true
    for prop in a.computed_style:
        val other = _draw_ir_patch_style_value(b, prop.key)
        if other == nil:
            return true
        if other != prop.value:
            return true
    false
```

On a 27-command round-trip fixture (`test/01_unit/lib/common/ui/draw_ir_patch_spec.spl`,
"round-trips a mixed ~30-command composition..."), this reported spurious
`style_changed == true` for `computed_style` entries that were byte-identical
("red" == "red") — **but only under `bin/simple test`**. The exact same
composition, walked with `bin/simple run` (a small standalone probe script),
and a manual field-by-field comparison loop printed inline as debug output
*inside the same `simple test` run*, both agreed the values were equal. Only
the path through the `text?`-returning lookup + `== nil` / `!=` comparison
disagreed.

## Fix applied (new code only)

`_draw_ir_patch_style_changed` in `draw_ir_patch.spl` was rewritten to avoid
returning/comparing a nilable value, using a raw double-loop membership
check instead:

```
fn _draw_ir_patch_style_changed(a: DrawIrCommand, b: DrawIrCommand) -> bool:
    if a.computed_style.len() != b.computed_style.len():
        return true
    for prop in a.computed_style:
        var matched = false
        for other in b.computed_style:
            if other.key == prop.key and other.value == prop.value:
                matched = true
        if not matched:
            return true
    false
```

After this change, `test/01_unit/lib/common/ui/draw_ir_patch_spec.spl` went
from 10/11 to 11/11 under `bin/simple test`, with no change under
`bin/simple run` (which was already green both before and after — confirming
the bug is specific to the daemon evaluator, not the algorithm).

## Known-identical latent defect NOT fixed (scope boundary)

`src/lib/common/ui/draw_ir_diff.spl`'s existing `_draw_ir_style_changed` /
`_draw_ir_style_value` pair has the **exact same shape**:

```
fn _draw_ir_style_value(command: DrawIrCommand, key: text) -> text?:
    for prop in command.computed_style:
        if prop.key == key:
            return prop.value
    nil

fn _draw_ir_style_changed(a: DrawIrCommand, b: DrawIrCommand) -> bool:
    if a.computed_style.len() != b.computed_style.len():
        return true
    for prop in a.computed_style:
        val other = _draw_ir_style_value(b, prop.key)
        if other == nil:
            return true
        if other != prop.value:
            return true
    false
```

This is presumed to carry the identical latent defect (unverified at scale —
`draw_ir_diff_spec.spl`'s fixtures are 2 commands, too small to trigger it).
It was **not** changed as part of this lane: the DRAWIR-PATCH task
constraint (Verdict item 4,
`doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md`)
requires `draw_ir_diff.spl`'s report/API to stay unchanged for existing
consumers pending patch-application being proven; touching an internal
helper's algorithm, even for a bugfix, was judged out of scope for that
additive-only slice and is left for a dedicated follow-up.

## Suggested follow-up

1. Rewrite `_draw_ir_style_changed`/`_draw_ir_style_value` in
   `draw_ir_diff.spl` using the same raw double-loop pattern, with a
   regression spec using a computed_style-bearing fixture at ~20+ elements
   to actually exercise the daemon-scale path (the current 2-element fixture
   would not catch a regression).
2. Investigate the general class: does `simple test`'s evaluator handle
   `T?`-returning loop-then-compare patterns incorrectly at moderate
   collection scale generally, or is this specific to `text?`? A
   minimal-repro micro-benchmark (grow an array size N, same shape,
   binary-search the N where the two evaluators start disagreeing) would
   turn this from "observed once" into "characterized," matching the
   project's "recurring problem -> team + tests" policy.
3. Grep for the same `for ... return value / nil` + `== nil` comparison shape
   elsewhere in `src/lib/**` — this is a common idiom and other call sites
   may have the same masked defect at scale.
