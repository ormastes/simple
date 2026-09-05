# Engine2d Text Specification

> Tests covering Engine2D Text Rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Text Specification

## Scenarios

### Engine2D Text Rendering

#### cpu backend

#### draw_text renders non-zero pixels in the glyph area

- draw_text renders non-zero pixels in the glyph area
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_text renders non-zero pixels in the glyph area")
# draw_text uses FontRenderer (8x16 bitmap + bearing offsets), so
# we scan the first 20x20 region for any non-black pixel rather
# than asserting a specific coordinate.
var engine = Engine2D.create_with_backend(50, 20, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_text(0, 0, "A", rgb(255, 255, 255), 14)
engine.present()
val pixels = engine.read_pixels()
val found = any_nonblack_in_region(pixels, 0, 0, 20, 20, 50)
expect(found).to_equal(true)
engine.shutdown()
```

</details>

#### draw_text leaves pixels outside the glyph area unchanged

- draw_text leaves pixels outside the glyph area unchanged
   - Expected: color_r(p) equals `0`
   - Expected: color_g(p) equals `0`
   - Expected: color_b(p) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_text leaves pixels outside the glyph area unchanged")
# Draw "A" at (0,0) with font_size=14.  The glyph fits in roughly
# 8x14 px.  A pixel at (45, 18) is well outside that — must remain
# the black background.
var engine = Engine2D.create_with_backend(50, 20, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_text(0, 0, "A", rgb(255, 255, 255), 14)
engine.present()
val pixels = engine.read_pixels()
val p = text_pixel_at(pixels, 45, 18, 50)
expect(color_r(p)).to_equal(0)
expect(color_g(p)).to_equal(0)
expect(color_b(p)).to_equal(0)
engine.shutdown()
```

</details>

#### draw_text_bg fills background color where the glyph bit is OFF

- draw_text_bg fills background color where the glyph bit is OFF


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_text_bg fills background color where the glyph bit is OFF")
# "A" row 0: 0b01110 — x=0 (col 0) is OFF, so that pixel should
# take the background color (green = rgb(0,255,0)), not the fg.
# At scale=1, font_size=7, the cell is 6px wide x 7px tall.
# draw_text_bg uses bilinear AA so the pure-bg pixel is at
# the leftmost column of the first row (x=0, y=0), which maps
# to font col 0 with coverage 0 → pure bg.
var engine = Engine2D.create_with_backend(50, 20, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_text_bg(0, 0, "A", rgb(255, 255, 255), rgb(0, 255, 0), 7)
engine.present()
val pixels = engine.read_pixels()
# x=0, y=0 → font col 0 row 0 → coverage 0 (OFF) → pure bg green
val p = text_pixel_at(pixels, 0, 0, 50)
expect(color_g(p)).to_be_greater_than(0)
# Red component should be much less than green (bg is green, fg is white)
expect(color_r(p)).to_be_less_than(color_g(p))
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine2d_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D Text Rendering.
- Engine2D Text Rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `064ed1f40e0b9858bfc5060c631a310e46c4febbd196f4dbbe9a20da9ac2e0a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `064ed1f40e0b9858bfc5060c631a310e46c4febbd196f4dbbe9a20da9ac2e0a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `064ed1f40e0b9858bfc5060c631a310e46c4febbd196f4dbbe9a20da9ac2e0a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/engine2d_text_spec.spl
mirror: doc/06_spec/integration/rendering/engine2d_text_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine2d_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine2d_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine2d_text_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine2d_text_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_text renders non-zero pixels in the glyph area' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_text_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_text leaves pixels outside the glyph area unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_text_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_text_bg fills background color where the glyph bit is OFF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
