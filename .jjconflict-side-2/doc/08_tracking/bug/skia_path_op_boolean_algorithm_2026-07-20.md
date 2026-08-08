# Skia path_op boolean polygon ops: 2 of 6 examples fail

**Date:** 2026-07-20
**Category:** GENUINE-BUG (pure computational geometry, not a rendering/pixel test)
**Spec:** `test/unit/lib/skia/path_op_spec.spl` (4/6 passing)
**Command:** `SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/lib/skia/path_op_spec.spl --no-session-daemon`

## Symptom

`path_op(a, b, op)` (`src/lib/skia/feature/path_op/boolean.spl`, exercised
via `use std.skia.feature.path_op.{PathOp, path_op}`) implements Union /
Intersect / Difference / Xor over `SkPath` rectangles, and the spec checks
results purely via `SkPath.contains(x, y)` point-membership and
`SkPath.bounds()` — deliberately avoiding pixel/rendering assertions
(see the spec's own docstring: "robust against minor algorithm differences
... choice of EvenOdd vs Winding fill rule"). This is genuine computational
geometry logic, not a contested rendering test.

2 of the 6 `it` blocks fail (`Passed: 4, Failed: 2` per the runner's Test
Summary); I was not able to isolate exactly which 2 of the 6 without
per-example diagnostic output (the `simple test` runner does not print
individual assertion failures for this spec — see the general "test runner
detail" caveat in `doc/07_guide/infra/testing.md` § "Runner Operational
Caveats", `Results:` line is the only authoritative summary here). The 6
candidates, by `it` name:

1. `Union of two overlapping rects produces a path whose bbox equals the outer union bbox`
2. `Union of two disjoint rects produces a path containing both centers`
3. `Intersect of two overlapping rects contains only the overlap`
4. `Intersect of two disjoint rects is empty`
5. `Difference: rect minus centered smaller rect does NOT contain smaller rect center`
6. `Xor of two overlapping rects does NOT contain the overlap center`

## Root-cause hypothesis

Not diagnosed in depth (out of time budget for this pass — `boolean.spl`'s
polygon-clipping algorithm needs a dedicated read). Prime suspects given the
test names: disjoint-shape handling (case 2/4 — does the algorithm correctly
produce two disconnected sub-paths, or does it degenerate to a single
bounding path / empty result when inputs don't overlap?) and/or
Difference/Xor carve-out correctness (case 5/6) given Union/Intersect on
*overlapping* rects (cases 1/3) are the most heavily-trodden code paths and
thus more likely to already be correct.

## Suggested next step

Re-run with a small standalone `bin/simple run` repro per candidate (mirror
the pattern used for `math3d_cos_taylor_precision_2026-07-20.md`) printing
`u.contains(...)`/`u.bounds()` values directly to bisect which 2 of the 6
actually fail and get concrete expected-vs-actual numbers before touching
`boolean.spl`.
