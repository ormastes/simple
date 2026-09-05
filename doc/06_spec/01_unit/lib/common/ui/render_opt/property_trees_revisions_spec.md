# Property Trees Revisions Specification

> Tests covering PropertyTrees.create / PaintChunks.create start empty and quiescent, paint_chunks_property_rev unchanged input produces identical rev (idempotent), single node mutation bumps only the affected node's revision (count assertion), paint_chunks_raster count is proportional to revisions that matter, not to every dirty flag, revisions_mark is monotonic and never reuses a rev, revisions_chunk_grouping_rev is stable under reorder of unrelated nodes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Property Trees Revisions Specification

## Scenarios

### PropertyTrees.create / PaintChunks.create start empty and quiescent

#### fresh trees and chunks report zero revisions and zero chunks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fresh trees and chunks report zero revisions and zero chunks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fresh trees and chunks report zero revisions and zero chunks")
val t = PropertyTrees.create()
val c = PaintChunks.create()
assert_true(t.revision(PT_CLIP) == 0)
assert_true(t.revision(PT_EFFECT) == 0)
assert_true(c.chunk_count == 0)
assert_true(c.rebuild_count == 0)
assert_true(paint_chunks_property_rev(t) == 0)
```

</details>

### paint_chunks_property_rev unchanged input produces identical rev (idempotent)

#### repeated calls with no mutation return the same value

- repeated calls with no mutation return the same value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated calls with no mutation return the same value")
val t = make_scene()
assert_true(paint_chunks_property_rev(t) == paint_chunks_property_rev(t))
assert_true(paint_chunks_property_rev(t) == paint_chunks_property_rev(t))
```

</details>

#### a TRANSFORM-only mutation leaves property_rev unchanged

- a TRANSFORM-only mutation leaves property_rev unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a TRANSFORM-only mutation leaves property_rev unchanged")
val t = make_scene()
val before = paint_chunks_property_rev(t)
assert_true(t.set_translate(1, 200, 20) == PT_OK)
assert_true(t.set_translate(1, 300, 20) == PT_OK)
val after = paint_chunks_property_rev(t)
assert_true(before == after)
```

</details>

#### re-applying an unchanged CLIP payload does not bump the revision (set_payload no-op guard)

- re-applying an unchanged CLIP payload does not bump the revision (set_payload no-op guard)


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-applying an unchanged CLIP payload does not bump the revision (set_payload no-op guard)")
# Mirrors set_translate's no-op guard: a caller that re-applies the
# SAME clip/effect/scroll value every frame (e.g. re-deriving it from
# unrelated layout each frame) must not force paint-chunk regrouping
# every frame -- only a real value change may bump the revision.
val t = make_scene()
# node 3 is the second CLIP node added in make_scene, at (5, 5)
assert_true(t.node_revision(3) == 0)
val before = paint_chunks_property_rev(t)
assert_true(t.set_payload(3, 5, 5) == PT_OK)
assert_true(t.node_revision(3) == 0)
assert_true(t.revision(PT_CLIP) == 0)
assert_true(paint_chunks_property_rev(t) == before)
# a real change still bumps it, proving the guard isn't a blanket no-op
assert_true(t.set_payload(3, 9, 9) == PT_OK)
assert_true(t.node_revision(3) == 1)
assert_true(paint_chunks_property_rev(t) == before + 1)
```

</details>

### single node mutation bumps only the affected node's revision (count assertion)

#### mutating one CLIP node bumps only that node, not its sibling clip node

- mutating one CLIP node bumps only that node, not its sibling clip node


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mutating one CLIP node bumps only that node, not its sibling clip node")
val t = make_scene()
# node 3 is the second CLIP node added in make_scene
assert_true(t.node_revision(2) == 0)
assert_true(t.node_revision(3) == 0)
assert_true(t.set_payload(3, 9, 9) == PT_OK)
assert_true(t.node_revision(3) == 1)
# sibling clip node and the unrelated effect/transform nodes stay at 0
assert_true(t.node_revision(2) == 0)
assert_true(t.node_revision(0) == 0)
assert_true(t.node_revision(1) == 0)
assert_true(t.node_revision(4) == 0)
# exactly one PT_CLIP bump recorded, not two
assert_true(t.revision(PT_CLIP) == 1)
```

</details>

### paint_chunks_raster count is proportional to revisions that matter, not to every dirty flag

#### an EVENT-only mark raises dirty accounting but triggers zero rebuilds

- an EVENT-only mark raises dirty accounting but triggers zero rebuilds


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an EVENT-only mark raises dirty accounting but triggers zero rebuilds")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
val primed: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(primed.rastered_count == 3)

# EVENT never propagates into PAINT/CLIP/RESOURCE (see revisions.spl
# matrix), so it must raise dirty-flag accounting without moving the
# chunk-grouping revision at all.
assert_true(r.mark(0, REV_EVENT) == REV_OK)
assert_true(r.mark_count > 0)
assert_true(revisions_chunk_grouping_rev(r) == 0)

val after: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(after.rastered_count == 0)
assert_true(after.skipped_count == 3)
assert_true(after.bytes_painted == 0)
```

</details>

#### a RESOURCE mark that DOES reach paint rasters every chunk together

- a RESOURCE mark that DOES reach paint rasters every chunk together


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a RESOURCE mark that DOES reach paint rasters every chunk together")
val t = make_scene()
val c = make_chunks()
val r = RenderRevisions.create(4)
val primed: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(primed.rastered_count == 3)
assert_true(r.mark(0, REV_RESOURCE) == REV_OK)
assert_true(revisions_chunk_grouping_rev(r) > 0)
val after: RasterStats = paint_chunks_raster(c, t, r, 1, 1, 1, 1, 1)
assert_true(after.rastered_count == 3)
assert_true(after.skipped_count == 0)
```

</details>

### revisions_mark is monotonic and never reuses a rev

#### repeated marks on the same kind strictly increase its revision counter

- repeated marks on the same kind strictly increase its revision counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated marks on the same kind strictly increase its revision counter")
val r = RenderRevisions.create(3)
assert_true(r.revision(REV_PAINT) == 0)
var prev: u32 = r.revision(REV_PAINT)
var i: i64 = 0
while i < 5:
    assert_true(revisions_mark(r, i % 3, REV_PAINT) == REV_OK)
    val cur = r.revision(REV_PAINT)
    # strictly greater than the previous value: monotonic, and a
    # constant-return sabotage of revisions_mark (never touching the
    # counter) fails this immediately on the second iteration
    assert_true(cur > prev)
    prev = cur
    i = i + 1
assert_true(r.revision(REV_PAINT) == 5)
```

</details>

#### distinct successive marks never repeat an already-seen revision value

- distinct successive marks never repeat an already-seen revision value


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinct successive marks never repeat an already-seen revision value")
val r = RenderRevisions.create(2)
assert_true(revisions_mark(r, 0, REV_LAYOUT) == REV_OK)
val v1 = r.revision(REV_LAYOUT)
assert_true(revisions_mark(r, 1, REV_LAYOUT) == REV_OK)
val v2 = r.revision(REV_LAYOUT)
assert_true(revisions_mark(r, 0, REV_LAYOUT) == REV_OK)
val v3 = r.revision(REV_LAYOUT)
assert_true(v1 != v2)
assert_true(v2 != v3)
assert_true(v1 != v3)
```

</details>

### revisions_chunk_grouping_rev is stable under reorder of unrelated nodes

#### sums PAINT+CLIP+RESOURCE regardless of the order the marks were applied in

- sums PAINT+CLIP+RESOURCE regardless of the order the marks were applied in


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums PAINT+CLIP+RESOURCE regardless of the order the marks were applied in")
val r1 = RenderRevisions.create(4)
assert_true(r1.mark(0, REV_PAINT) == REV_OK)
assert_true(r1.mark(2, REV_CLIP) == REV_OK)
assert_true(r1.mark(3, REV_RESOURCE) == REV_OK)

val r2 = RenderRevisions.create(4)
assert_true(r2.mark(3, REV_RESOURCE) == REV_OK)
assert_true(r2.mark(0, REV_PAINT) == REV_OK)
assert_true(r2.mark(2, REV_CLIP) == REV_OK)

assert_true(revisions_chunk_grouping_rev(r1) == revisions_chunk_grouping_rev(r2))
```

</details>

#### interleaving unrelated TRANSFORM/EVENT marks does not change the grouping rev

- interleaving unrelated TRANSFORM/EVENT marks does not change the grouping rev


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interleaving unrelated TRANSFORM/EVENT marks does not change the grouping rev")
val r1 = RenderRevisions.create(4)
assert_true(r1.mark(0, REV_PAINT) == REV_OK)
assert_true(r1.mark(2, REV_CLIP) == REV_OK)
val base = revisions_chunk_grouping_rev(r1)

val r2 = RenderRevisions.create(4)
assert_true(r2.mark(1, REV_TRANSFORM) == REV_OK)
assert_true(r2.mark(0, REV_PAINT) == REV_OK)
assert_true(r2.mark(3, REV_EVENT) == REV_OK)
assert_true(r2.mark(2, REV_CLIP) == REV_OK)

assert_true(revisions_chunk_grouping_rev(r2) == base)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PropertyTrees.create / PaintChunks.create start empty and quiescent, paint_chunks_property_rev unchanged input produces identical rev (idempotent), single node mutation bumps only the affected node's revision (count assertion), paint_chunks_raster count is proportional to revisions that matter, not to every dirty flag, revisions_mark is monotonic and never reuses a rev, revisions_chunk_grouping_rev is stable under reorder of unrelated nodes.
- PropertyTrees.create / PaintChunks.create start empty and quiescent
- paint_chunks_property_rev unchanged input produces identical rev (idempotent)
- single node mutation bumps only the affected node's revision (count assertion)
- paint_chunks_raster count is proportional to revisions that matter, not to every dirty flag
- revisions_mark is monotonic and never reuses a rev
- revisions_chunk_grouping_rev is stable under reorder of unrelated nodes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `c0b07ce443e327fabb419fff32ba5cde107a8a1d7967b8554d77f3fed0b9a374`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0b07ce443e327fabb419fff32ba5cde107a8a1d7967b8554d77f3fed0b9a374`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0b07ce443e327fabb419fff32ba5cde107a8a1d7967b8554d77f3fed0b9a374`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fresh trees and chunks report zero revisions and zero chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repeated calls with no mutation return the same value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/render_opt/property_trees_revisions_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a TRANSFORM-only mutation leaves property_rev unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
