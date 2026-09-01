# font_renderer_placement_spec

> Purpose: Prove that font renderer text placement into a pixel buffer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# font_renderer_placement_spec

Purpose: Prove that font renderer text placement into a pixel buffer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that font renderer text placement into a pixel buffer.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### font renderer text placement into a pixel buffer

#### places 'AB' at (4,8) size 16 inside the expected two glyph cells

- Verify: places 'AB' at (4,8) size 16 inside the expected two glyph cells
   - Expected: ink_in_x_range(buf, 64, 40, 0, 4) equals `0`
   - Expected: ink_in_x_range(buf, 64, 40, 20, 64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: places 'AB' at (4,8) size 16 inside the expected two glyph cells")
# @req: REQ-LIB-NOGC-SYNC-MUT-001
val r = FontRenderer.bitmap_only()
var buf = zero_buffer(64 * 40)
buf = r.render_text(buf, 64, 40, 4, 8, "AB", 0xFFFFFFFF, 16)
val bb = ink_bbox(buf, 64, 40)
assert_true(bb[4] > 0)
# ink stays inside the two 8x16 cells starting at (4,8)
assert_true(bb[0] >= 4)
assert_true(bb[2] <= 4 + 16 - 1)
assert_true(bb[1] >= 8)
assert_true(bb[3] <= 8 + 16 - 1)
# advance accumulation: both glyph cells carry ink
assert_true(ink_in_x_range(buf, 64, 40, 4, 12) > 0)
assert_true(ink_in_x_range(buf, 64, 40, 12, 20) > 0)
# nothing left of x or right of the second cell
expect(ink_in_x_range(buf, 64, 40, 0, 4)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(ink_in_x_range(buf, 64, 40, 20, 64)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### doubles the occupied box at 2x scale (size 32)

- Verify: doubles the occupied box at 2x scale (size 32)
   - Expected: bb32[0] equals `bb16[0] * 2`
   - Expected: bb32[1] equals `bb16[1] * 2`
   - Expected: bb32[2] equals `bb16[2] * 2 + 1`
   - Expected: bb32[3] equals `bb16[3] * 2 + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: doubles the occupied box at 2x scale (size 32)")
val r = FontRenderer.bitmap_only()
var buf16 = zero_buffer(80 * 40)
buf16 = r.render_text(buf16, 80, 40, 0, 0, "AB", 0xFFFFFFFF, 16)
val bb16 = ink_bbox(buf16, 80, 40)
var buf32 = zero_buffer(80 * 40)
buf32 = r.render_text(buf32, 80, 40, 0, 0, "AB", 0xFFFFFFFF, 32)
val bb32 = ink_bbox(buf32, 80, 40)
assert_true(bb32[4] > 0)
# box position and size scale by 2 exactly (pixel doubling)
expect(bb32[0]).to_equal(bb16[0] * 2)
expect(bb32[1]).to_equal(bb16[1] * 2)
expect(bb32[2]).to_equal(bb16[2] * 2 + 1)
expect(bb32[3]).to_equal(bb16[3] * 2 + 1)
# second glyph advance doubled: ink present beyond x=16
assert_true(ink_in_x_range(buf32, 80, 40, 16, 32) > 0)
```

</details>

#### paints nothing for an empty string

- Verify: paints nothing for an empty string
   - Expected: ink_bbox(buf, 32, 32)[4] equals `0`
   - Expected: buf.len() equals `32 * 32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: paints nothing for an empty string")
val r = FontRenderer.bitmap_only()
var buf = zero_buffer(32 * 32)
buf = r.render_text(buf, 32, 32, 5, 5, "", 0xFFFFFFFF, 16)
expect(ink_bbox(buf, 32, 32)[4]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(buf.len()).to_equal(32 * 32)
```

</details>

#### clips out-of-bounds placement instead of corrupting the buffer

- Verify: clips out-of-bounds placement instead of corrupting the buffer
   - Expected: buf.len() equals `32 * 32`
   - Expected: ink_bbox(buf, 32, 32)[4] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: clips out-of-bounds placement instead of corrupting the buffer")
val r = FontRenderer.bitmap_only()
var buf = zero_buffer(32 * 32)
buf = r.render_text(buf, 32, 32, -100, -100, "A", 0xFFFFFFFF, 16)
buf = r.render_text(buf, 32, 32, 1000, 1000, "A", 0xFFFFFFFF, 16)
expect(buf.len()).to_equal(32 * 32)
expect(ink_bbox(buf, 32, 32)[4]).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### partially clips a glyph straddling the buffer edge

- Verify: partially clips a glyph straddling the buffer edge
   - Expected: buf.len() equals `8 * 8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: partially clips a glyph straddling the buffer edge")
val r = FontRenderer.bitmap_only()
var buf = zero_buffer(8 * 8)
buf = r.render_text(buf, 8, 8, 4, -8, "A", 0xFFFFFFFF, 16)
expect(buf.len()).to_equal(8 * 8)
val bb = ink_bbox(buf, 8, 8)
# any ink drawn must be within the visible region right of x=4
if bb[4] > 0:
    assert_true(bb[0] >= 4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-LIB-NOGC-SYNC-MUT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8fd52232598d927b44ab6f1b68454d42d6bda59095366bd294728082a5d34c79`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8fd52232598d927b44ab6f1b68454d42d6bda59095366bd294728082a5d34c79`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8fd52232598d927b44ab6f1b68454d42d6bda59095366bd294728082a5d34c79`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places 'AB' at (4,8) size 16 inside the expected two glyph cells' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'doubles the occupied box at 2x scale (size 32)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/text_layout/font_renderer_placement_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints nothing for an empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
