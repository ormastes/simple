# Engine2D region-limited readback equivalence

> D9 (`doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md`) calls out the per-glass-rect FULL-FRAME `read_pixels_with_source()` in `_engine2d_draw_ir_render_batch_embedded` (the `samples_parent and embedding_opacity < 1000` branch): with N translucent/backdrop-sampling batches per frame that is N whole-framebuffer reads, when only one small rect is ever needed. The fix routes that call site through a new seam, `_engine2d_read_pixels_region`, which today is the DEFAULT implementation (read the whole frame once, crop on the host) but establishes the API a future backend-specific device-side region read can drop in behind without touching call sites again.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D region-limited readback equivalence

D9 (`doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md`) calls out the per-glass-rect FULL-FRAME `read_pixels_with_source()` in `_engine2d_draw_ir_render_batch_embedded` (the `samples_parent and embedding_opacity < 1000` branch): with N translucent/backdrop-sampling batches per frame that is N whole-framebuffer reads, when only one small rect is ever needed. The fix routes that call site through a new seam, `_engine2d_read_pixels_region`, which today is the DEFAULT implementation (read the whole frame once, crop on the host) but establishes the API a future backend-specific device-side region read can drop in behind without touching call sites again.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A -- implementation evidence for D9 of the unified 2D |
| Plan | doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

D9 (`doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md`)
calls out the per-glass-rect FULL-FRAME `read_pixels_with_source()` in
`_engine2d_draw_ir_render_batch_embedded` (the `samples_parent and
embedding_opacity < 1000` branch): with N translucent/backdrop-sampling
batches per frame that is N whole-framebuffer reads, when only one small rect
is ever needed. The fix routes that call site through a new seam,
`_engine2d_read_pixels_region`, which today is the DEFAULT implementation
(read the whole frame once, crop on the host) but establishes the API a
future backend-specific device-side region read can drop in behind without
touching call sites again.

This spec is the correctness argument for making that swap: it proves
`_engine2d_read_pixels_region(engine, x, y, w, h)` returns pixels IDENTICAL
to reading the whole frame with `engine.read_pixels_with_source()` and
cropping it by hand -- both for an in-bounds rect and for a rect that
partially runs off the framebuffer edge (the half-open, zero-fill-at-edge
convention `_engine2d_draw_ir_parent_region_pixels` already implements).

**Requirements:** N/A -- implementation evidence for D9 of the unified 2D
engine plan, not a numbered product requirement.

**Plan:** doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md

## Scenarios

### Engine2D region-limited readback (_engine2d_read_pixels_region)

#### returns the same pixels as a full-frame read cropped by hand, for an in-bounds rect

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the same pixels as a full-frame read cropped by hand, for an in-bounds rect
   - Expected: region.pixels equals `expected`
   - Expected: region.pixel_count equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the same pixels as a full-frame read cropped by hand, for an in-bounds rect")
var engine = Engine2D.create_with_backend(4, 4, "cpu")
engine.clear(BG)
engine.draw_rect_filled(0, 0, 2, 2, RED)
engine.draw_rect_filled(2, 0, 2, 2, GREEN)
engine.draw_rect_filled(0, 2, 2, 2, BLUE)
engine.draw_rect_filled(2, 2, 2, 2, YELLOW)

# Independent ground truth: read the WHOLE frame once and index the
# 2x3 rect at (1,1) by hand, row-major -- no shared helper with the
# function under test.
val full = engine.read_pixels_with_source()
val expected = [
    full.pixels[1 * 4 + 1], full.pixels[1 * 4 + 2],
    full.pixels[2 * 4 + 1], full.pixels[2 * 4 + 2],
    full.pixels[3 * 4 + 1], full.pixels[3 * 4 + 2]
]

val region = _engine2d_read_pixels_region(engine, 1, 1, 2, 3)

expect(region.pixels).to_equal(expected)
expect(region.pixel_count).to_equal(6)
engine.shutdown()
```

</details>

#### fills out-of-bounds columns/rows with 0, matching the full-frame crop edge rule

- fills out-of-bounds columns/rows with 0, matching the full-frame crop edge rule
   - Expected: region.pixels equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fills out-of-bounds columns/rows with 0, matching the full-frame crop edge rule")
var engine = Engine2D.create_with_backend(3, 3, "cpu")
engine.clear(RED)

# x=-1 column is out of range on every row -> 0. y=3 row is entirely
# out of range (engine is only 3 tall) -> 0,0,0. This is the same
# half-open, zero-fill edge behavior read_pixels_with_source() plus a
# hand crop would produce.
val region = _engine2d_read_pixels_region(engine, -1, 2, 3, 2)

expect(region.pixels).to_equal([
    0u32, RED, RED,
    0u32, 0u32, 0u32
])
engine.shutdown()
```

</details>

#### matches _engine2d_draw_ir_parent_region_pixels exactly for the full-frame rect

- matches _engine2d_draw_ir_parent_region_pixels exactly for the full-frame rect
   - Expected: region.pixels equals `cropped_by_hand`
   - Expected: region.pixels equals `full.pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches _engine2d_draw_ir_parent_region_pixels exactly for the full-frame rect")
var engine = Engine2D.create_with_backend(6, 5, "cpu")
engine.clear(BG)
engine.draw_rect_filled(1, 1, 3, 2, GREEN)

val full = engine.read_pixels_with_source()
val cropped_by_hand = _engine2d_draw_ir_parent_region_pixels(
    full, 6, 5, 0, 0, 6, 5)
val region = _engine2d_read_pixels_region(engine, 0, 0, 6, 5)

expect(region.pixels).to_equal(cropped_by_hand)
expect(region.pixels).to_equal(full.pixels)
engine.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `N/A -- implementation evidence for D9 of the unified 2D`
- **Plan:** `doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6f934f867e9fedb51c48be86731d923d793bea2fd1156e6474a61d3d0966afd7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f934f867e9fedb51c48be86731d923d793bea2fd1156e6474a61d3d0966afd7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f934f867e9fedb51c48be86731d923d793bea2fd1156e6474a61d3d0966afd7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the same pixels as a full-frame read cropped by hand, for an in-bounds rect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills out-of-bounds columns/rows with 0, matching the full-frame crop edge rule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_read_pixels_region_equivalence_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches _engine2d_draw_ir_parent_region_pixels exactly for the full-frame rect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
