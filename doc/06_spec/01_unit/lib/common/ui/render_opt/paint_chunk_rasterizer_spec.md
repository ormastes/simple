# Paint Chunk Rasterizer Specification

> Tests covering F4 paint_rect edge cases: zero-area, negative-origin, empty chunk list, O3 paint-chunk rasterizer: dirty chunks paint, skipped chunks stay untouched.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paint Chunk Rasterizer Specification

## Scenarios

### F4 paint_rect edge cases: zero-area, negative-origin, empty chunk list

#### zero-area rects (w=0 or h=0) paint nothing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- zero-area rects (w=0 or h=0) paint nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-area rects (w=0 or h=0) paint nothing")
val buf = ChunkRasterBuffer.create(10, 10)
paint_rect(buf, 2, 2, 0, 3, 0xFFFF0000)
paint_rect(buf, 2, 2, 3, 0, 0xFFFF0000)
var i: i64 = 0
var any_nonzero = false
while i < 100:
    if buf.pixels[i.to_i32()] != 0:
        any_nonzero = true
    i = i + 1
assert_false(any_nonzero)
```

</details>

#### fully out-of-bounds negative-y rect paints nothing (row clip works)

- fully out-of-bounds negative-y rect paints nothing (row clip works)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fully out-of-bounds negative-y rect paints nothing (row clip works)")
val buf = ChunkRasterBuffer.create(10, 10)
paint_rect(buf, 2, -5, 3, 2, 0xFFFF0000)
var i: i64 = 0
var any_nonzero = false
while i < 100:
    if buf.pixels[i.to_i32()] != 0:
        any_nonzero = true
    i = i + 1
assert_false(any_nonzero)
```

</details>

#### negative-origin x clips to the buffer instead of bleeding into the preceding row (FIXED: see doc/08_tracking/bug/paint_rect_negative_x_row_bleed_2026-08-07.md)

- negative-origin x clips to the buffer instead of bleeding into the preceding row (FIXED: see doc/08_tracking/bug/paint_rect_negative_x_row_bleed_2026-08-07.md)


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative-origin x clips to the buffer instead of bleeding into the preceding row (FIXED: see doc/08_tracking/bug/paint_rect_negative_x_row_bleed_2026-08-07.md)")
# `paint_rect` now clips the fill span per row to [0, buf.stride) in x,
# the same way it already clipped `py` to [0, buf.height) in y. Before
# the fix, x=-3 made `row_offset` land in the PRECEDING row's tail and
# the fill bled forward across the row boundary; now it is clamped to
# the intersection of [x, x+w) with [0, stride), i.e. [0, 2).
val buf = ChunkRasterBuffer.create(10, 10)
paint_rect(buf, -3, 2, 5, 1, 0xFFFF0000)
# Row 1 (the row ABOVE the target row 2) must stay completely
# untouched -- no bleed at all.
assert_true(buf.get(7, 1) == 0)
assert_true(buf.get(8, 1) == 0)
assert_true(buf.get(9, 1) == 0)
# Row 2 (the intended target row) is clipped to columns [0, 2):
# requested span [-3, 2) intersected with [0, 10) is [0, 2).
assert_true(buf.get(0, 2) == 0xFFFF0000)
assert_true(buf.get(1, 2) == 0xFFFF0000)
assert_true(buf.get(2, 2) == 0)
```

</details>

#### negative-x rect fully left of the buffer paints nothing and touches no neighbouring row

- negative-x rect fully left of the buffer paints nothing and touches no neighbouring row


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative-x rect fully left of the buffer paints nothing and touches no neighbouring row")
val buf = ChunkRasterBuffer.create(10, 10)
paint_rect(buf, -8, 3, 5, 1, 0xFFFF0000)
var i: i64 = 0
var any_nonzero = false
while i < 100:
    if buf.pixels[i.to_i32()] != 0:
        any_nonzero = true
    i = i + 1
assert_false(any_nonzero)
```

</details>

#### x + w overflowing the right edge clips instead of writing into the next row

- x + w overflowing the right edge clips instead of writing into the next row


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("x + w overflowing the right edge clips instead of writing into the next row")
val buf = ChunkRasterBuffer.create(10, 10)
paint_rect(buf, 7, 4, 5, 1, 0xFFFF0000)
# Requested span [7, 12) intersected with [0, 10) is [7, 10).
assert_true(buf.get(7, 4) == 0xFFFF0000)
assert_true(buf.get(8, 4) == 0xFFFF0000)
assert_true(buf.get(9, 4) == 0xFFFF0000)
# Row 5 (the row BELOW the target row 4) must stay untouched -- no
# bleed from the overflowing tail wrapping into the next row.
assert_true(buf.get(0, 5) == 0)
assert_true(buf.get(1, 5) == 0)
assert_true(buf.get(2, 5) == 0)
```

</details>

#### negative-y rect with partial row overlap paints only in-bounds rows, no wrap-around bleed

- negative-y rect with partial row overlap paints only in-bounds rows, no wrap-around bleed


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative-y rect with partial row overlap paints only in-bounds rows, no wrap-around bleed")
val buf = ChunkRasterBuffer.create(10, 10)
paint_rect(buf, 2, -1, 3, 3, 0xFFFF0000)
# Requested rows y=-1,0,1; only rows 0 and 1 are in bounds.
assert_true(buf.get(2, 0) == 0xFFFF0000)
assert_true(buf.get(3, 0) == 0xFFFF0000)
assert_true(buf.get(4, 0) == 0xFFFF0000)
assert_true(buf.get(2, 1) == 0xFFFF0000)
# The last row of the buffer must not have been touched by the
# negative-y clip (no wrap-around from the skipped row=-1).
assert_true(buf.get(2, 9) == 0)
```

</details>

#### paint_chunk_rasterizer_run with an empty chunk list rasters nothing and reports zero counts

- paint_chunk_rasterizer_run with an empty chunk list rasters nothing and reports zero counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paint_chunk_rasterizer_run with an empty chunk list rasters nothing and reports zero counts")
val trees = make_scene()
val chunks = PaintChunks.create()
val rects = make_rects()
val revs = RenderRevisions.create(4)
val buf = ChunkRasterBuffer.create(40, 10)
val stats = paint_chunk_rasterizer_run(chunks, rects, trees, revs, buf,
                                        1, 1, 1, 1, 1)
assert_true(stats.rastered_count == 0)
assert_true(stats.skipped_count == 0)
var i: i64 = 0
var any_nonzero = false
while i < 400:
    if buf.pixels[i.to_i32()] != 0:
        any_nonzero = true
    i = i + 1
assert_false(any_nonzero)
```

</details>

### O3 paint-chunk rasterizer: dirty chunks paint, skipped chunks stay untouched

#### frame 1 paints the 3 existing chunks; frame 2's newly-added 4th chunk is the ONLY one that paints

- frame 1 paints the 3 existing chunks; frame 2's newly-added 4th chunk is the ONLY one that paints


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame 1 paints the 3 existing chunks; frame 2's newly-added 4th chunk is the ONLY one that paints")
val trees = make_scene()
val chunks = PaintChunks.create()
chunks.add_chunk_sized(1, 0, 1, 2, 0, 7, 0, 100)
chunks.add_chunk_sized(2, 0, 1, 2, 0, 7, 1, 100)
chunks.add_chunk_sized(3, 0, 1, 2, 0, 7, 2, 100)
val rects = make_rects()
val revs = RenderRevisions.create(4)
val buf = ChunkRasterBuffer.create(40, 10)

# Frame 1: 3 chunks exist and are all dirty (fresh keys default to 0).
val stats1 = paint_chunk_rasterizer_run(chunks, rects, trees, revs, buf,
                                         1, 1, 1, 1, 1)
assert_true(stats1.rastered_count == 3)
assert_true(stats1.skipped_count == 0)
val frame1 = snapshot(buf)
assert_true(frame1[0] == 0xFFFF0000)
assert_true(frame1[15] == 0xFF00FF00)
assert_true(frame1[25] == 0xFF0000FF)
# band 3 (yellow, index 30..39) is still buffer-zero: chunk 4 does
# not exist yet.
assert_true(frame1[35] == 0)

# Frame 2: a 4th chunk is added, everything else about the frame is
# unchanged (same generation args) — this is the ONLY thing that
# should make anything dirty this call.
chunks.add_chunk_sized(4, 0, 1, 2, 0, 7, 3, 100)
val stats2 = paint_chunk_rasterizer_run(chunks, rects, trees, revs, buf,
                                         1, 1, 1, 1, 1)
assert_true(stats2.rastered_count == 1)
assert_true(stats2.skipped_count == 3)

val frame2 = snapshot(buf)
# REAL PIXEL COMPARISON: exactly one band (the new chunk's) differs,
# every other band's pixels are byte-identical to frame 1.
assert_true(count_changed_bands(frame1, frame2) == 1)
assert_true(frame2[35] == 0xFFFFFF00)
assert_true(frame2[0] == 0xFFFF0000)
assert_true(frame2[15] == 0xFF00FF00)
assert_true(frame2[25] == 0xFF0000FF)
```

</details>

#### SABOTAGE: forcing every chunk to rasterize every frame breaks the exactly-one-band invariant

- SABOTAGE: forcing every chunk to rasterize every frame breaks the exactly-one-band invariant


<details>
<summary>Executable SSpec</summary>

Runnable source: 59 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE: forcing every chunk to rasterize every frame breaks the exactly-one-band invariant")
val trees = make_scene()
val chunks = PaintChunks.create()
chunks.add_chunk_sized(1, 0, 1, 2, 0, 7, 0, 100)
chunks.add_chunk_sized(2, 0, 1, 2, 0, 7, 1, 100)
chunks.add_chunk_sized(3, 0, 1, 2, 0, 7, 2, 100)
val rects = make_rects()
val revs = RenderRevisions.create(4)
val buf = ChunkRasterBuffer.create(40, 10)

val _stats1 = paint_chunk_rasterizer_run(chunks, rects, trees, revs, buf,
                                          1, 1, 1, 1, 1)
val frame1 = snapshot(buf)

chunks.add_chunk_sized(4, 0, 1, 2, 0, 7, 3, 100)

# Sabotage: bypass the dirty-skip decision entirely and unconditionally
# repaint EVERY rect with a distinguishable "wrong" colour, exactly
# what a broken/no-skip rasterizer would do every frame regardless of
# which chunks actually went stale. A same-colour repaint of an
# already-fresh band would be invisible to a pixel diff and would
# prove nothing, so the sabotage colour must differ from frame 1's.
var i: i64 = 0
while i < rects.rect_count:
    paint_rect(buf, rects.rect_x[i], rects.rect_y[i],
              rects.rect_w[i], rects.rect_h[i], 0xFF000000)
    i = i + 1

val frame2_sabotaged = snapshot(buf)
val changed_sabotaged = count_changed_bands(frame1, frame2_sabotaged)
# All 4 bands now differ, not just the newly-added chunk 4's: the
# "only the newly-dirty chunk changed" invariant the real path
# guarantees goes red under the sabotage, exactly because the skip
# logic was bypassed. Assert the failure condition explicitly.
assert_true(changed_sabotaged == 4)
assert_true(changed_sabotaged != 1)

# Restore the real (non-sabotaged) path on a fresh buffer and prove it
# is back to reporting exactly 1 rastered / 3 skipped and exactly 1
# changed band — the sabotage above was a bypass of this module, not
# a change to its real skip logic.
val real_trees = make_scene()
val real_chunks = PaintChunks.create()
real_chunks.add_chunk_sized(1, 0, 1, 2, 0, 7, 0, 100)
real_chunks.add_chunk_sized(2, 0, 1, 2, 0, 7, 1, 100)
real_chunks.add_chunk_sized(3, 0, 1, 2, 0, 7, 2, 100)
val real_revs = RenderRevisions.create(4)
val real_buf = ChunkRasterBuffer.create(40, 10)
val _real1 = paint_chunk_rasterizer_run(real_chunks, rects, real_trees,
                                         real_revs, real_buf, 1, 1, 1, 1, 1)
val real_frame1 = snapshot(real_buf)
real_chunks.add_chunk_sized(4, 0, 1, 2, 0, 7, 3, 100)
val stats_real = paint_chunk_rasterizer_run(real_chunks, rects, real_trees,
                                              real_revs, real_buf, 1, 1, 1, 1, 1)
assert_true(stats_real.rastered_count == 1)
assert_true(stats_real.skipped_count == 3)
val real_frame2 = snapshot(real_buf)
assert_true(count_changed_bands(real_frame1, real_frame2) == 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering F4 paint_rect edge cases: zero-area, negative-origin, empty chunk list, O3 paint-chunk rasterizer: dirty chunks paint, skipped chunks stay untouched.
- F4 paint_rect edge cases: zero-area, negative-origin, empty chunk list
- O3 paint-chunk rasterizer: dirty chunks paint, skipped chunks stay untouched

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e2f47ee8f6bcd676a8625c3439613605432632e583bf7e9bc7b068bf9ce90341`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2f47ee8f6bcd676a8625c3439613605432632e583bf7e9bc7b068bf9ce90341`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2f47ee8f6bcd676a8625c3439613605432632e583bf7e9bc7b068bf9ce90341`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero-area rects (w=0 or h=0) paint nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fully out-of-bounds negative-y rect paints nothing (row clip works)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/paint_chunk_rasterizer_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negative-origin x clips to the buffer instead of bleeding into the preceding row (FIXED: see doc/08_tracking/bug/paint_rect_negative_x_row_bleed_2026-08-07.md)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
