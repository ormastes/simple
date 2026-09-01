# tile_paint_parity_spec

> Tile paint parity spec (T2 CPU lane gate)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tile_paint_parity_spec

Tile paint parity spec (T2 CPU lane gate)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tile paint parity spec (T2 CPU lane gate)

Pixel-parity oracle for the CPU tile-render-culling lane: the tiled painter
must produce a visible region identical to the classic paint() on the same
pipeline, while the tile counters prove real op-level culling (no
fabrication: ops_painted/tiles_skipped are recorded by paint_tiled itself).

Fixtures: a 95%-offscreen tall scrolling document, a mixed
text/border/shadow document compared over the FULL framebuffer, and a tall
document with a full-width opaque overlay driving T3 occlusion.

Plan gate: ops-painted <= 30% of baseline on the offscreen/occluded
fixtures. Plan: doc/03_plan/ui/rendering/tile_render_culling_plan.md

@tag: rendering, simple-web, tiles, culling, parity

## Scenarios

### tile paint parity

#### matches the classic painter on the 95%-offscreen tall doc at scroll 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the classic painter on the 95%-offscreen tall doc at scroll 0
   - Expected: _parity_at(_tall_doc_html(50), TALL_DOC_H, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the classic painter on the 95%-offscreen tall doc at scroll 0")
expect(_parity_at(_tall_doc_html(50), TALL_DOC_H, 0)).to_equal(0)
```

</details>

#### matches the classic painter on the tall doc at mid scroll

- matches the classic painter on the tall doc at mid scroll
   - Expected: _parity_at(_tall_doc_html(50), TALL_DOC_H, 2432) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the classic painter on the tall doc at mid scroll")
expect(_parity_at(_tall_doc_html(50), TALL_DOC_H, 2432)).to_equal(0)
```

</details>

#### matches the classic painter on the tall doc near the end

- matches the classic painter on the tall doc near the end
   - Expected: _parity_at(_tall_doc_html(50), TALL_DOC_H, TALL_DOC_H - VIEW_H) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the classic painter on the tall doc near the end")
expect(_parity_at(_tall_doc_html(50), TALL_DOC_H, TALL_DOC_H - VIEW_H)).to_equal(0)
```

</details>

#### is byte-identical over the FULL framebuffer on the mixed document

- is byte-identical over the FULL framebuffer on the mixed document
   - Expected: _diff_rows(base, tiled, DOC_W, 0, 512) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is byte-identical over the FULL framebuffer on the mixed document")
# Viewport covers the whole (short) document: every tile is live, so
# any diff would expose a non-conservative cull or a raster change.
val html = _mixed_doc_html()
val base = simple_web_layout_render_html_software_pixels_tile_lane(
    html, DOC_W, 512, 0, 512, false
)
val tiled = simple_web_layout_render_html_software_pixels_tile_lane(
    html, DOC_W, 512, 0, 512, true
)
expect(_diff_rows(base, tiled, DOC_W, 0, 512)).to_equal(0)
```

</details>

#### stays pixel-identical while occlusion-culling under the opaque overlay

- stays pixel-identical while occlusion-culling under the opaque overlay
   - Expected: _parity_at(_occluded_doc_html(), TALL_DOC_H, 1024) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stays pixel-identical while occlusion-culling under the opaque overlay")
expect(_parity_at(_occluded_doc_html(), TALL_DOC_H, 1024)).to_equal(0)
```

</details>

### tile culling effectiveness

#### paints at most 30% of baseline ops on the deep scrolled doc

- paints at most 30% of baseline ops on the deep scrolled doc
   - Expected: tiled.len() > 0 is true
   - Expected: total > 0 is true
   - Expected: painted > 0 is true
   - Expected: painted * 100 <= total * 30 is true
   - Expected: tile_stats_tiles_skipped() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints at most 30% of baseline ops on the deep scrolled doc")
tile_stats_reset()
val html = _tall_doc_html(100)
val tiled = simple_web_layout_render_html_software_pixels_tile_lane(
    html, DOC_W, DEEP_DOC_H, 4992, VIEW_H, true
)
expect(tiled.len() > 0).to_equal(true)
val total = tile_stats_ops_total()
val painted = tile_stats_ops_painted()
print "[tile-bench] fixture=deep_97pct_offscreen ops_total={total} ops_painted={painted} tiles_live={tile_stats_tiles_live()} tiles_skipped={tile_stats_tiles_skipped()}"
expect(total > 0).to_equal(true)
expect(painted > 0).to_equal(true)
# Plan T5 gate: ops-painted <= 30% of baseline on the K=20 fixture.
expect(painted * 100 <= total * 30).to_equal(true)
expect(tile_stats_tiles_skipped() > 0).to_equal(true)
```

</details>

#### occlusion-culls tiles fully covered by the opaque overlay

- occlusion-culls tiles fully covered by the opaque overlay
   - Expected: tiled.len() > 0 is true
   - Expected: occluded >= 2 is true
   - Expected: painted * 100 <= total * 30 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("occlusion-culls tiles fully covered by the opaque overlay")
tile_stats_reset()
val html = _occluded_doc_html()
val tiled = simple_web_layout_render_html_software_pixels_tile_lane(
    html, DOC_W, TALL_DOC_H, 1024, VIEW_H, true
)
expect(tiled.len() > 0).to_equal(true)
val occluded = tile_stats_tiles_occluded()
val painted = tile_stats_ops_painted()
val total = tile_stats_ops_total()
print "[tile-bench] fixture=occluded_overlay ops_total={total} ops_painted={painted} tiles_occluded={occluded}"
# The 256x512 overlay fully covers 2 tiles.
expect(occluded >= 2).to_equal(true)
expect(painted * 100 <= total * 30).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `878c6510e6d3080454eb56b6c245965bcf873c736ff5f6cd43e755ce433cc621`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `878c6510e6d3080454eb56b6c245965bcf873c736ff5f6cd43e755ce433cc621`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `878c6510e6d3080454eb56b6c245965bcf873c736ff5f6cd43e755ce433cc621`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the classic painter on the 95%-offscreen tall doc at scroll 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.spl:135:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the classic painter on the tall doc at mid scroll' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_paint_parity_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the classic painter on the tall doc near the end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
