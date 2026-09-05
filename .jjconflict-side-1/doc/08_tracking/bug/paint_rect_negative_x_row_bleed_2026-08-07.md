# `paint_rect` negative-origin x bleeds into the preceding row instead of clipping

- **Status**: resolved 2026-08-07
- **File**: `src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl:136-143` (`paint_rect`)
- **Found while**: F4 (render_2d_vulkan_functional_coverage_plan_2026-08-07.md),
  writing the "zero-area and negative-origin rects paint nothing" `it`.

## What the plan assumed vs. what actually happens

The plan (`render_2d_vulkan_functional_coverage_plan_2026-08-07.md` Unit F4)
assumed negative-origin rects "paint nothing" — the same as zero-area rects.
That is true only for a rect whose `y` puts every row fully out of bounds
(`paint_rect`'s `py >= 0 and py < buf.height` check handles that case
correctly — verified, see spec `it "fully out-of-bounds negative-y rect
paints nothing"`).

It is **not** true for negative `x`. `paint_rect` clips `py` per row but never
clips `x`/`row_offset` against the buffer stride, and the primitive it calls,
`oracle_fill_const` (`src/lib/common/gpu/engine2d/scalar_oracle.spl:159`),
performs no bounds check of its own — it just writes `count` consecutive
`u32` cells starting at `offset` with no notion of "row" or "stride" at all.

So for a rect with negative `x`, `row_offset = py * stride + x` is computed
once per row and can land **before** that row's first cell — i.e. inside the
tail of the *previous* row in the flat pixel buffer — and the fill then
writes forward across that row boundary into the intended row's head. The
result is genuine cross-row pixel corruption of a row the rect was never
supposed to touch, not "paints nothing" and not "clips to the target row."

## Reproduction (see spec)

`test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl`,
describe block `"F4 paint_rect edge cases..."`, it `"REAL BEHAVIOR (not plan
assumption): negative-origin x bleeds into the PRECEDING row instead of
clipping"`:

```
val buf = ChunkRasterBuffer.create(10, 10)
paint_rect(buf, -3, 2, 5, 1, 0xFFFF0000)
# row 1 (ABOVE the target row 2), columns 7,8,9 get corrupted:
assert_true(buf.get(7, 1) == 0xFFFF0000)
assert_true(buf.get(8, 1) == 0xFFFF0000)
assert_true(buf.get(9, 1) == 0xFFFF0000)
# row 2 (the intended target) only gets columns 0,1 painted, not 5-wide,
# not clipped-to-nothing either:
assert_true(buf.get(0, 2) == 0xFFFF0000)
assert_true(buf.get(1, 2) == 0xFFFF0000)
assert_true(buf.get(2, 2) == 0)
```

Probed directly via `bin/simple run` before the spec was written (interpreter
engine), same result.

## Unblock condition (met)

`paint_rect` now clips the effective fill span per row against
`[0, buf.stride)` in x (`x0 = max(x, 0)`, `x1 = min(x + w, buf.stride)`, skip
the row's fill when `x1 <= x0`) before calling `oracle_fill_const`, the same
way it already clipped `py` in y. The audit of the same function for
symmetric top/right/bottom clips found: the top/bottom clip (`py >= 0 and py
< buf.height`) was already correct and untouched; the new x1 clip also covers
the right-edge overflow case (`x + w > buf.stride`), which had the same
unclipped-`row_offset`-length defect on the far side and is now fixed by the
same two-line change. `paint_chunk_rasterizer_run`'s only other call site of
`paint_rect` is unaffected in shape (same signature, same per-chunk stats
accounting) — it only ever receives smaller, in-bounds rects in its existing
callers, so no behavior change there beyond the same safety clip.

## Before/after pixel evidence

Both runs: `paint_rect(buf, -3, 2, 5, 1, 0xFFFF0000)` on a fresh
`ChunkRasterBuffer.create(10, 10)` (buggy request: x=-3, w=5, so requested
span is columns [-3, 2) of row 2).

| pixel | before (buggy) | after (fixed) |
|---|---|---|
| `buf.get(7, 1)` (row ABOVE target, bled-into) | `0xFFFF0000` (corrupted) | `0` (untouched) |
| `buf.get(8, 1)` | `0xFFFF0000` (corrupted) | `0` (untouched) |
| `buf.get(9, 1)` | `0xFFFF0000` (corrupted) | `0` (untouched) |
| `buf.get(0, 2)` (target row, in-bounds part of the span) | `0xFFFF0000` | `0xFFFF0000` (unchanged — correct) |
| `buf.get(1, 2)` | `0xFFFF0000` | `0xFFFF0000` (unchanged — correct) |
| `buf.get(2, 2)` | `0` | `0` (unchanged — correct) |

The "before" column is the behavior this bug doc originally pinned via spec
assertions (now replaced — see below); the "after" column is the current
`test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl`
assertions, verified green with the deployed self-hosted `bin/simple`:

```
bin/simple test test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl
...
Results: 9 total, 9 passed, 0 failed
```

The spec's `"REAL BEHAVIOR (not plan assumption): ..."` pinning `it` was
replaced with `"negative-origin x clips to the buffer instead of bleeding
into the preceding row (FIXED: ...)"`, and three new cases were added:
fully-off-left negative x paints nothing, right-edge overflow clips instead
of bleeding into the next row, and a partial-overlap negative-y rect paints
only its in-bounds rows with no wrap-around bleed.
