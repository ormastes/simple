# `paint_rect` negative-origin x bleeds into the preceding row instead of clipping

- **Status**: open
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

## Unblock condition

`paint_rect` should clip the effective fill span per row against
`[0, buf.stride)` in x (e.g. compute `x0 = max(x, 0)`, `x1 = min(x + w,
buf.stride)`, skip if `x1 <= x0`) before calling `oracle_fill_const`, the same
way it already clips `py` in y. Not fixed here — F4's job was to characterize
and pin real behavior with a spec, not silently patch a rasterizer module
that has other untouched call sites (`paint_chunk_rasterizer_run`) this fix
would also affect the accounting of.
