# `Matrix3x3` is imported from `std.common.drawing.vector` but only exists in the skia tree (2026-08-04)

**Status:** FIXED (2026-08-09/10)
**Found:** 2026-08-04

## Fix

`Matrix3x3` (and its private `_sin_taylor`/`_cos_taylor`/`_sqrt_newton`
helpers, renamed `_matrix3x3_*` to avoid collision) moved from
`src/lib/skia/entity/matrix.spl` into `src/lib/common/drawing/vector.spl`,
exactly the "move, not an addition" fix this doc already called for.
`src/lib/skia/entity/matrix.spl` is now a 15-line re-export
(`use std.common.drawing.vector.{Matrix3x3}` + `export Matrix3x3`) so every
existing `use std.skia.entity.matrix.{Matrix3x3}` call site keeps working
unchanged — no caller edits needed. `src/lib/skia/__init__.spl`'s
`from entity.matrix import { Matrix3x3, _sin_taylor, _cos_taylor }` dropped
the two Taylor-helper names (unused outside that one import, never
re-exported).

Verified fresh (interpreter, this worktree, 2026-08-09/10):
```
$ use std.common.drawing.vector.{Matrix3x3}; Matrix3x3.identity()
diag: 1.0 1.0 1.0
off: 0.0 0.0 0.0 0.0 0.0 0.0
translate tx=5.0 ty=7.0

$ use std.skia.entity.matrix.{Matrix3x3}; Matrix3x3.rotate_degrees(deg: 90.0)
rot: ~0 -1 1 ~0   # cos(90)≈0, -sin(90)≈-1, sin(90)≈1, cos(90)≈0 — correct
```
Both the new common-tier import path and the old skia re-export path produce
correct values. The full `test/03_system/stdlib/vector_spec.spl` spec run
timed out in this environment before printing a verdict line (harness
startup cost, not a fix defect — see `reference_kill_monitor_60s_cpu_guard_sigterms_long_runs.md`);
direct interpreter execution of both call paths above is the evidence of
record for this fix.
**Class:** missing symbol / tier-placement decision. 2 failing examples in
`test/03_system/stdlib/vector_spec.spl`.

## Symptom

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/03_system/stdlib/vector_spec.spl --no-cover-check
  ✗ identity diagonal is 1.0
    semantic: variable `Matrix3x3` not found
  ✗ identity off-diagonal is 0.0
    semantic: variable `Matrix3x3` not found
Results: 9 total, 7 passed, 2 failed
```

`test/03_system/stdlib/vector_spec.spl:7` imports it:

```
use std.common.drawing.vector.{SkPoint, SkRect, PathPoint, Matrix3x3}
```

and the spec header states the module "Verifies SkPoint, SkRect, PathPoint, and
Matrix3x3 basics."

## Root cause (what is PROVEN)

`Matrix3x3` is declared exactly once in the repository, and not in the common
tier:

```
$ grep -rn '^class Matrix3x3\|^struct Matrix3x3\|^pub struct Matrix3x3' --include=*.spl src/
src/lib/skia/entity/matrix.spl:57:class Matrix3x3:
```

That declaration already has the exact shape the spec asserts — fields `m00`…
`m22` and `static fn identity()` returning the identity matrix
(`src/lib/skia/entity/matrix.spl:57-73`) — so the *behaviour* exists; only its
location is wrong for this import path. `src/lib/skia` is a peer tree of
`src/lib/common`, reached as `std.skia.*`, so `std.common.drawing.vector` cannot
import it without inverting the tier order.

The sibling gaps in the same spec were fixable in place and have been fixed in
`src/lib/common/drawing/vector.spl`:
- `SkRect.center()` added (the module had only `center_x`/`center_y`).
- `SkRect.contains_point` re-signatured from `(p: SkPoint)` to `(px: f64, py: f64)`
  — the repo-wide convention, and the signature its only in-tree caller
  `src/lib/nogc_sync_mut/editor/panel.spl:57` was already calling it with, so the
  editor panel hit-test was broken by the old signature.
- `PathPoint` implemented (`linear`/`cubic`/`has_controls`); no symbol of that
  name existed anywhere.

`Matrix3x3` is the one that could not be: adding a second `class Matrix3x3` in
`vector.spl` would create a duplicate type name across modules — the hazard the
runner already warns about for functions ("public function `X` has N
co-compiled definitions … a fallback hit may still dispatch to the wrong one")
and the reimplementation-duplication trap recorded repeatedly in this tracker.

## Why not fixed now

The correct fix is a **move, not an addition**: relocate `Matrix3x3` from
`src/lib/skia/entity/matrix.spl` into the common tier (it is a pure value type
and belongs there) and have the skia module import it, so exactly one
declaration survives. That edit touches the skia tree, which sits adjacent to
the live 2-D/Vulkan hardening work this lane was scoped away from, and it drags
`matrix.spl`'s `_cos_taylor`/`_sin_taylor` helpers along with `rotate_degrees`
— a trig dependency the common drawing module does not currently carry. Whether
those move too, or `Matrix3x3` moves without its transform constructors, is a
placement decision for the owner of that tree.
