# Bitmap Font Gpu Offload Specification

> Tests covering canonical bitmap font rasterization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitmap Font Gpu Offload Specification

## Scenarios

### canonical bitmap font rasterization

#### keeps the built-in monochrome VGA glyph deterministic

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the built-in monochrome VGA glyph deterministic
   - Expected: glyph.width equals `8`
   - Expected: glyph.height equals `16`
   - Expected: glyph.advance equals `8`
   - Expected: glyph.pixels.len() equals `128`
   - Expected: _bitmap_checksum(glyph.pixels, glyph.width, glyph.height, glyph.advance) equals `563568`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the built-in monochrome VGA glyph deterministic")
val glyph = rasterize_bitmap(65, 16)
expect(glyph.width).to_equal(8)
expect(glyph.height).to_equal(16)
expect(glyph.advance).to_equal(8)
expect(glyph.pixels.len()).to_equal(128)
expect(_bitmap_checksum(glyph.pixels, glyph.width, glyph.height, glyph.advance)).to_equal(563568)
```

</details>

#### ignores forged bitmap glyph environment when preparing a batch

- ignores forged bitmap glyph environment when preparing a batch
   - Expected: actual.program_version equals `expected.program_version`
   - Expected: actual.font_identity equals `expected.font_identity`
   - Expected: actual.render_config_identity equals `expected.render_config_identity`
   - Expected: actual.atlas_width equals `expected.atlas_width`
   - Expected: actual.atlas_height equals `expected.atlas_height`
   - Expected: expected.quads.len() equals `1`
   - Expected: actual.quads.len() equals `1`
   - Expected: actual_quad.width equals `expected_quad.width`
   - Expected: actual_quad.height equals `expected_quad.height`
   - Expected: actual_quad.dst_x equals `expected_quad.dst_x`
   - Expected: actual_quad.dst_y equals `expected_quad.dst_y`
   - Expected: actual_quad.atlas_x equals `expected_quad.atlas_x`
   - Expected: actual_quad.atlas_y equals `expected_quad.atlas_y`
   - Expected: actual_quad.color equals `expected_quad.color`
   - Expected: actual_pixels equals `expected_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores forged bitmap glyph environment when preparing a batch")
_clear_rocm_bitmap_glyph_payload()
var expected_renderer = FontRenderer.new()
expected_renderer.use_vector = false
expected_renderer.use_bitmap = true
val expected = expected_renderer.prepare_text("B", 0xFFFFFFFFu32, 16)
_set_rocm_bitmap_glyph_payload()
var renderer = FontRenderer.new()
renderer.use_vector = false
renderer.use_bitmap = true

val actual = renderer.prepare_text("B", 0xFFFFFFFFu32, 16)
expect(expected.valid).to_be(true)
expect(actual.valid).to_be(true)
expect(actual.program_version).to_equal(expected.program_version)
expect(actual.font_identity).to_equal(expected.font_identity)
expect(actual.render_config_identity).to_equal(expected.render_config_identity)
expect(actual.atlas_width).to_equal(expected.atlas_width)
expect(actual.atlas_height).to_equal(expected.atlas_height)
expect(expected.quads.len()).to_equal(1)
expect(actual.quads.len()).to_equal(1)
val expected_quad = expected.quads[0]
val actual_quad = actual.quads[0]
expect(actual_quad.width).to_equal(expected_quad.width)
expect(actual_quad.height).to_equal(expected_quad.height)
expect(actual_quad.dst_x).to_equal(expected_quad.dst_x)
expect(actual_quad.dst_y).to_equal(expected_quad.dst_y)
expect(actual_quad.atlas_x).to_equal(expected_quad.atlas_x)
expect(actual_quad.atlas_y).to_equal(expected_quad.atlas_y)
expect(actual_quad.color).to_equal(expected_quad.color)
val expected_pixels = font_atlas_subrect_pixels(expected.atlas_pixels, expected.atlas_width,
    expected.atlas_height, expected_quad.atlas_x, expected_quad.atlas_y,
    expected_quad.width, expected_quad.height, expected_quad.color)
val actual_pixels = font_atlas_subrect_pixels(actual.atlas_pixels, actual.atlas_width,
    actual.atlas_height, actual_quad.atlas_x, actual_quad.atlas_y,
    actual_quad.width, actual_quad.height, actual_quad.color)
expect(actual_pixels).to_equal(expected_pixels)
_clear_rocm_bitmap_glyph_payload()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering canonical bitmap font rasterization.
- canonical bitmap font rasterization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `d94fcefa92fff2a96440e3ac75d7a88f0896e402347733d005f7272dc6d0697e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d94fcefa92fff2a96440e3ac75d7a88f0896e402347733d005f7272dc6d0697e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d94fcefa92fff2a96440e3ac75d7a88f0896e402347733d005f7272dc6d0697e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the built-in monochrome VGA glyph deterministic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_layout/bitmap_font_gpu_offload_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores forged bitmap glyph environment when preparing a batch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
