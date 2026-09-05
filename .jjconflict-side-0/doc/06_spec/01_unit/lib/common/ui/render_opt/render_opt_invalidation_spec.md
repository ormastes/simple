# Render Opt Invalidation Specification

> Tests covering O0 invalidation marks the minimal dependency set, O1 transform-only move: update + damage, no chunk rebuild, O2 paint_chunks_raster skips chunks whose cache key is unchanged, SABOTAGE: each O-lane gate goes red when its invariant is broken.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Opt Invalidation Specification

## Scenarios

### O0 invalidation marks the minimal dependency set

#### propagates STYLE to layout and paint and to nothing else

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- propagates STYLE to layout and paint and to nothing else


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates STYLE to layout and paint and to nothing else")
val r = RenderRevisions.create(4)
assert_true(r.mark(2, REV_STYLE) == REV_OK)
# positive count of what SHOULD change — a no-op impl cannot pass
assert_true(r.dirty_nodes(REV_STYLE) == 1)
assert_true(r.is_dirty(2, REV_STYLE))
assert_true(r.is_dirty(2, REV_LAYOUT))
assert_true(r.is_dirty(2, REV_PAINT))
# the untouched set is genuinely untouched: exactly 3 flags, not
# "at least the ones we asked about"
assert_true(r.total_dirty() == 3)
assert_true(r.is_dirty(2, REV_SEMANTIC) == false)
assert_true(r.is_dirty(2, REV_TRANSFORM) == false)
assert_true(r.is_dirty(2, REV_CLIP) == false)
assert_true(r.is_dirty(2, REV_RESOURCE) == false)
assert_true(r.is_dirty(2, REV_EVENT) == false)
```

</details>

#### leaves every OTHER node untouched

- leaves every OTHER node untouched


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves every OTHER node untouched")
val r = RenderRevisions.create(4)
assert_true(r.mark(2, REV_STYLE) == REV_OK)
# only node 2 is dirty in each propagated kind
assert_true(r.dirty_nodes(REV_PAINT) == 1)
assert_true(r.is_dirty(0, REV_PAINT) == false)
assert_true(r.is_dirty(1, REV_PAINT) == false)
assert_true(r.is_dirty(3, REV_PAINT) == false)
```

</details>

#### marks TRANSFORM alone — never paint (the load-bearing row)

- marks TRANSFORM alone — never paint (the load-bearing row)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks TRANSFORM alone — never paint (the load-bearing row)")
val r = RenderRevisions.create(4)
assert_true(r.mark(1, REV_TRANSFORM) == REV_OK)
assert_true(r.is_dirty(1, REV_TRANSFORM))
assert_true(r.total_dirty() == 1)
assert_true(r.is_dirty(1, REV_PAINT) == false)
assert_true(r.dirty_nodes(REV_PAINT) == 0)
assert_true(r.dirty_nodes(REV_LAYOUT) == 0)
```

</details>

#### propagates SEMANTIC through the full chain

- propagates SEMANTIC through the full chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates SEMANTIC through the full chain")
val r = RenderRevisions.create(4)
assert_true(r.mark(0, REV_SEMANTIC) == REV_OK)
assert_true(r.total_dirty() == 4)
assert_true(r.is_dirty(0, REV_SEMANTIC))
assert_true(r.is_dirty(0, REV_PAINT))
assert_true(r.is_dirty(0, REV_TRANSFORM) == false)
```

</details>

#### routes CLIP and RESOURCE to paint but not to layout

- routes CLIP and RESOURCE to paint but not to layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes CLIP and RESOURCE to paint but not to layout")
val r = RenderRevisions.create(4)
assert_true(r.mark(1, REV_CLIP) == REV_OK)
assert_true(r.is_dirty(1, REV_PAINT))
assert_true(r.is_dirty(1, REV_LAYOUT) == false)
assert_true(r.total_dirty() == 2)
val r2 = RenderRevisions.create(4)
assert_true(r2.mark(1, REV_RESOURCE) == REV_OK)
assert_true(r2.is_dirty(1, REV_PAINT))
assert_true(r2.total_dirty() == 2)
```

</details>

#### keeps EVENT out of the render chain entirely

- keeps EVENT out of the render chain entirely


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps EVENT out of the render chain entirely")
val r = RenderRevisions.create(4)
assert_true(r.mark(3, REV_EVENT) == REV_OK)
assert_true(r.total_dirty() == 1)
assert_true(r.dirty_nodes(REV_PAINT) == 0)
```

</details>

#### bumps revision counters and refuses bad input

- bumps revision counters and refuses bad input


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bumps revision counters and refuses bad input")
val r = RenderRevisions.create(2)
assert_true(r.revision(REV_PAINT) == 0)
assert_true(r.mark(0, REV_PAINT) == REV_OK)
assert_true(r.revision(REV_PAINT) == 1)
assert_true(r.mark(9, REV_PAINT) == REV_BAD_NODE)
assert_true(r.mark(0, 99) == REV_BAD_KIND)
# refusals raise nothing
assert_true(r.total_dirty() == 1)
```

</details>

#### mutates through the free-function form too

- mutates through the free-function form too


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mutates through the free-function form too")
val r = RenderRevisions.create(2)
assert_true(revisions_mark(r, 1, REV_LAYOUT) == REV_OK)
assert_true(r.is_dirty(1, REV_LAYOUT))
assert_true(r.is_dirty(1, REV_PAINT))
assert_true(r.total_dirty() == 2)
```

</details>

### O1 transform-only move: update + damage, no chunk rebuild

#### moves one node, damages two rects, and rebuilds zero chunks

- moves one node, damages two rects, and rebuilds zero chunks


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves one node, damages two rects, and rebuilds zero chunks")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
# prime the keys, then measure only what the move costs
assert_true(prime(c, t, r) == 3)
val rebuilds_before = c.rebuild_count
t.clear_damage()

assert_true(t.set_translate(1, 200, 20) == PT_OK)

# something DID change — positive counts, so a no-op cannot pass
assert_true(t.node_revision(1) == 1)
assert_true(t.revision(PT_TRANSFORM) == 1)
assert_true(t.damage_len == 2)
# vacated 100x50 plus newly occupied 100x50
assert_true(t.damage_area() == 10000)

# ...and no paint work followed from it
assert_true(paint_chunks_sync(c, t, r, 1, 1, 1, 1, 1) == 0)
assert_true(c.rebuild_count == rebuilds_before)
assert_true(r.dirty_nodes(REV_PAINT) == 0)
```

</details>

#### still rebuilds when a CLIP change actually regroups

- still rebuilds when a CLIP change actually regroups


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still rebuilds when a CLIP change actually regroups")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
assert_true(prime(c, t, r) == 3)
assert_true(t.set_payload(2, 5, 5) == PT_OK)
# the key is live, not inert — this is what stops the gate above
# from passing merely because nothing is ever rebuilt
assert_true(paint_chunks_sync(c, t, r, 1, 1, 1, 1, 1) == 3)
```

</details>

#### rebuilds when paint/clip/resource revisions move

- rebuilds when paint/clip/resource revisions move


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rebuilds when paint/clip/resource revisions move")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
assert_true(prime(c, t, r) == 3)
assert_true(r.mark(0, REV_PAINT) == REV_OK)
assert_true(paint_chunks_sync(c, t, r, 1, 1, 1, 1, 1) == 3)
```

</details>

#### rebuilds on theme, scale, viewport and capability generations

- rebuilds on theme, scale, viewport and capability generations


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rebuilds on theme, scale, viewport and capability generations")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
assert_true(prime(c, t, r) == 3)
assert_true(paint_chunks_sync(c, t, r, 1, 2, 1, 1, 1) == 3)
assert_true(paint_chunks_sync(c, t, r, 1, 2, 3, 1, 1) == 3)
assert_true(paint_chunks_sync(c, t, r, 1, 2, 3, 4, 1) == 3)
assert_true(paint_chunks_sync(c, t, r, 1, 2, 3, 4, 5) == 3)
# stable input, no further work
assert_true(paint_chunks_sync(c, t, r, 1, 2, 3, 4, 5) == 0)
```

</details>

#### is idempotent: re-syncing unchanged state costs nothing

- is idempotent: re-syncing unchanged state costs nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is idempotent: re-syncing unchanged state costs nothing")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
assert_true(prime(c, t, r) == 3)
assert_true(prime(c, t, r) == 0)
assert_true(prime(c, t, r) == 0)
```

</details>

#### refuses a translate on a non-transform node

- refuses a translate on a non-transform node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a translate on a non-transform node")
val t = make_scene()
assert_true(t.set_translate(2, 1, 1) == PT_WRONG_TREE)
assert_true(t.damage_len == 0)
```

</details>

#### records no damage for a move that does not move

- records no damage for a move that does not move


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records no damage for a move that does not move")
val t = make_scene()
assert_true(t.set_translate(1, 10, 20) == PT_OK)
assert_true(t.damage_len == 0)
assert_true(t.revision(PT_TRANSFORM) == 0)
```

</details>

### O2 paint_chunks_raster skips chunks whose cache key is unchanged

#### rasters every chunk once, then skips all of them once primed

- rasters every chunk once, then skips all of them once primed


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasters every chunk once, then skips all of them once primed")
val t = make_scene()
val c = PaintChunks.create()
c.add_chunk_sized(1, 1, 2, 3, 0, 7, 0, 1000)
c.add_chunk_sized(2, 1, 2, 3, 0, 7, 1, 1000)
c.add_chunk_sized(3, 1, 2, 3, 0, 8, 2, 1000)
c.add_chunk_sized(4, 1, 2, 3, 0, 8, 3, 1000)
c.add_chunk_sized(5, 1, 2, 3, 0, 9, 4, 1000)
val r = RenderRevisions.create(4)

val first: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(first.rastered_count == 5)
assert_true(first.skipped_count == 0)
assert_true(first.bytes_painted == 5000)

# three more "frames" with nothing damaged: whole-scene rework would
# keep rastering all 5; damage-proportional skip rasters none.
val f2: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(f2.rastered_count == 0)
assert_true(f2.skipped_count == 5)
assert_true(f2.bytes_painted == 0)
val f3: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(f3.rastered_count == 0)
assert_true(f3.skipped_count == 5)
val f4: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(f4.rastered_count == 0)
assert_true(f4.skipped_count == 5)
```

</details>

#### one small changed region rasters proportional to its own area, not the scene

- one small changed region rasters proportional to its own area, not the scene


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one small changed region rasters proportional to its own area, not the scene")
val t = make_scene()
val c = PaintChunks.create()
c.add_chunk_sized(1, 1, 2, 3, 0, 7, 0, 1000)
c.add_chunk_sized(2, 1, 2, 3, 0, 7, 1, 1000)
c.add_chunk_sized(3, 1, 2, 3, 0, 8, 2, 1000)
c.add_chunk_sized(4, 1, 2, 3, 0, 8, 3, 1000)
c.add_chunk_sized(5, 1, 2, 3, 0, 9, 4, 1000)
val r = RenderRevisions.create(4)
val primed: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(primed.rastered_count == 5)

# a small new region of content arrives (one 200-byte chunk); the
# other five chunks' keys are untouched — no global revision moved.
c.add_chunk_sized(6, 1, 2, 3, 0, 7, 5, 200)
val changed: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(changed.rastered_count == 1)
assert_true(changed.skipped_count == 5)
assert_true(changed.bytes_painted == 200)

# subsequent frames: the new chunk is now primed too, so the scene
# is fully quiescent again — proof the skip persists across frames.
val settled: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(settled.rastered_count == 0)
assert_true(settled.skipped_count == 6)
assert_true(settled.bytes_painted == 0)
```

</details>

#### a real regroup (clip change) rasters the whole scene, not just one chunk

- a real regroup (clip change) rasters the whole scene, not just one chunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a real regroup (clip change) rasters the whole scene, not just one chunk")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
assert_true(prime(c, t, r) == 3)
assert_true(t.set_payload(2, 5, 5) == PT_OK)
val stats: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(stats.rastered_count == 3)
assert_true(stats.skipped_count == 0)
```

</details>

### SABOTAGE: each O-lane gate goes red when its invariant is broken

#### SABOTAGE (O0): a TRANSFORM row that also marks PAINT breaks the one-column invariant

- SABOTAGE (O0): a TRANSFORM row that also marks PAINT breaks the one-column invariant


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE (O0): a TRANSFORM row that also marks PAINT breaks the one-column invariant")
# Real matrix: TRANSFORM marks column TRANSFORM only.
val real = RenderRevisions.create(4)
assert_true(real.mark(1, REV_TRANSFORM) == REV_OK)
assert_true(real.total_dirty() == 1)
assert_true(real.dirty_nodes(REV_PAINT) == 0)

# Sabotage: identical in every way except the TRANSFORM row, which
# now also marks PAINT — the exact regression the module's comment
# calls out as defeating the whole lane.
var revs: [u32] = []
var k: i64 = 0
while k < REV_KIND_COUNT:
    revs.push(0)
    k = k + 1
var flags: [u32] = []
var i: i64 = 0
while i < 4 * REV_KIND_COUNT:
    flags.push(0)
    i = i + 1
val bad_matrix: [u32] = [
    1, 1, 1, 1, 0, 0, 0, 0,
    0, 1, 1, 1, 0, 0, 0, 0,
    0, 0, 1, 1, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 1, 1, 0, 0, 0,
    0, 0, 0, 1, 0, 1, 0, 0,
    0, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 1
]
val sab = RenderRevisions(
    kind_rev: revs, node_dirty: flags, node_count: 4,
    prop: bad_matrix, mark_count: 0)
assert_true(sab.mark(1, REV_TRANSFORM) == REV_OK)
# The gate's expected values (1 and 0) are now both violated, so the
# gate above would fail. Assert the violation explicitly.
assert_true(sab.total_dirty() != 1)
assert_true(sab.total_dirty() == 2)
assert_true(sab.dirty_nodes(REV_PAINT) != 0)
assert_true(sab.dirty_nodes(REV_PAINT) == 1)
```

</details>

#### SABOTAGE (O1): folding PT_TRANSFORM into the chunk cache key rebuilds on every move

- SABOTAGE (O1): folding PT_TRANSFORM into the chunk cache key rebuilds on every move


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE (O1): folding PT_TRANSFORM into the chunk cache key rebuilds on every move")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
assert_true(prime(c, t, r) == 3)

val real_before = paint_chunks_property_rev(t)
val sab_before = real_before + t.revision(PT_TRANSFORM)
assert_true(t.set_translate(1, 200, 20) == PT_OK)
val real_after = paint_chunks_property_rev(t)
val sab_after = paint_chunks_property_rev(t) + t.revision(PT_TRANSFORM)

# Real key component: a transform-only move does not move it, so
# zero chunks go stale (§10 "transform-only move => zero repaint").
assert_true(real_after == real_before)
assert_true(paint_chunks_sync(c, t, r, 1, 1, 1, 1, 1) == 0)

# Sabotaged key component: it moved. Count how many chunks a key
# built on it would find stale — all of them.
assert_true(sab_after != sab_before)
var stale: i64 = 0
var i: i64 = 0
while i < c.chunk_count:
    if c.key_property_rev[i] != sab_after:
        stale = stale + 1
    i = i + 1
assert_true(stale != 0)
assert_true(stale == 3)
```

</details>

#### SABOTAGE (O2): an unconditional raster breaks the quiescent-frame zero

- SABOTAGE (O2): an unconditional raster breaks the quiescent-frame zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SABOTAGE (O2): an unconditional raster breaks the quiescent-frame zero")
val t = make_scene()
val c = PaintChunks.create()
c.add_chunk_sized(1, 1, 2, 3, 0, 7, 0, 1000)
c.add_chunk_sized(2, 1, 2, 3, 0, 7, 1, 1000)
c.add_chunk_sized(3, 1, 2, 3, 0, 8, 2, 1000)
c.add_chunk_sized(4, 1, 2, 3, 0, 8, 3, 1000)
c.add_chunk_sized(5, 1, 2, 3, 0, 9, 4, 1000)
val r = RenderRevisions.create(4)
val primed: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(primed.rastered_count == 5)

# Real path on a quiescent frame: nothing rastered, nothing painted.
val quiet: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(quiet.rastered_count == 0)
assert_true(quiet.bytes_painted == 0)

# Sabotage: skip the staleness decision entirely, exactly what a
# rasterizer that ignores the cache key would do.
var sab_count: i64 = 0
var sab_bytes: i64 = 0
var i: i64 = 0
while i < c.chunk_count:
    sab_count = sab_count + 1
    sab_bytes = sab_bytes + c.chunk_area[i]
    i = i + 1
assert_true(sab_count != 0)
assert_true(sab_count == 5)
assert_true(sab_bytes != 0)
assert_true(sab_bytes == 5000)

# The real path is unaffected by the bypass and still quiescent.
val after: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(after.rastered_count == 0)
assert_true(after.skipped_count == 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering O0 invalidation marks the minimal dependency set, O1 transform-only move: update + damage, no chunk rebuild, O2 paint_chunks_raster skips chunks whose cache key is unchanged, SABOTAGE: each O-lane gate goes red when its invariant is broken.
- O0 invalidation marks the minimal dependency set
- O1 transform-only move: update + damage, no chunk rebuild
- O2 paint_chunks_raster skips chunks whose cache key is unchanged
- SABOTAGE: each O-lane gate goes red when its invariant is broken

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `fd43812d9c6ec3c75728e38344c87192a25d616acdaed7c0582c487141d8a7c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd43812d9c6ec3c75728e38344c87192a25d616acdaed7c0582c487141d8a7c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd43812d9c6ec3c75728e38344c87192a25d616acdaed7c0582c487141d8a7c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates STYLE to layout and paint and to nothing else' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves every OTHER node untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/render_opt_invalidation_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks TRANSFORM alone — never paint (the load-bearing row)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
