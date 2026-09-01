# Font Glyph Slot Loop Specification

> Tests covering backend glyph slot-probe loop.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Glyph Slot Loop Specification

## Scenarios

### backend glyph slot-probe loop

#### finds a bitmap glyph published at slot 5 (beyond the old 4-slot unroll cap)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds a bitmap glyph published at slot 5 (beyond the old 4-slot unroll cap)
   - Expected: glyph.width equals `2`
   - Expected: glyph.height equals `2`
   - Expected: glyph.advance equals `3`
   - Expected: stats.gpu_returned_glyphs equals `1`
   - Expected: stats.cpu_fallback_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds a bitmap glyph published at slot 5 (beyond the old 4-slot unroll cap)")
_set_rocm_bitmap_slot5_payload()
reset_bitmap_font_raster_stats()
val glyph = rasterize_bitmap_accelerated(66, 16)
_clear_rocm_bitmap_slot5_payload()
# The env-published glyph is 2x2/advance 3; the CPU-fallback VGA glyph
# would be 8x16/advance 8 — so these dimensions prove slot 5 was probed.
expect(glyph.width).to_equal(2)
expect(glyph.height).to_equal(2)
expect(glyph.advance).to_equal(3)
val stats = bitmap_font_accelerator_stats()
expect(stats.gpu_returned_glyphs).to_equal(1)
expect(stats.cpu_fallback_hits).to_equal(0)
```

</details>

#### falls back to CPU when GLYPH_COUNT is huge but no slot matches (cap bounds the probe)

- falls back to CPU when GLYPH_COUNT is huge but no slot matches (cap bounds the probe)
   - Expected: glyph.width equals `8`
   - Expected: glyph.height equals `16`
   - Expected: stats.cpu_fallback_hits equals `1`
   - Expected: stats.gpu_returned_glyphs equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to CPU when GLYPH_COUNT is huge but no slot matches (cap bounds the probe)")
_set_rocm_bitmap_slot5_payload()
rt_env_set("ROCM_BITMAP_FONT_GLYPH_COUNT", "1000000")
reset_bitmap_font_raster_stats()
# Codepoint 67 matches no published slot; the loop must terminate at the
# slot cap and take the deterministic CPU fallback.
val glyph = rasterize_bitmap_accelerated(67, 16)
_clear_rocm_bitmap_slot5_payload()
expect(glyph.width).to_equal(8)
expect(glyph.height).to_equal(16)
val stats = bitmap_font_accelerator_stats()
expect(stats.cpu_fallback_hits).to_equal(1)
expect(stats.gpu_returned_glyphs).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering backend glyph slot-probe loop.
- backend glyph slot-probe loop

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

- Canonical SPipe generation for source `a6bd225b3bc4bdce1a22f26c99c9788815cfc0864a1b24b43061c6ddd5f44dac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6bd225b3bc4bdce1a22f26c99c9788815cfc0864a1b24b43061c6ddd5f44dac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6bd225b3bc4bdce1a22f26c99c9788815cfc0864a1b24b43061c6ddd5f44dac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a bitmap glyph published at slot 5 (beyond the old 4-slot unroll cap)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_layout/font_glyph_slot_loop_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to CPU when GLYPH_COUNT is huge but no slot matches (cap bounds the probe)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
