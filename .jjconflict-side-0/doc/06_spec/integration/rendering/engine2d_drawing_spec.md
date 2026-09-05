# Engine2d Drawing Specification

> Tests covering Engine2D Drawing Primitives.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Drawing Specification

## Scenarios

### Engine2D Drawing Primitives

#### cpu backend

#### draw_rect_filled fills correct region

- draw_rect_filled fills correct region
   - Expected: color_r(inside) equals `255`
   - Expected: color_g(inside) equals `0`
   - Expected: color_r(outside) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw_rect_filled fills correct region")
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_rect_filled(2, 2, 3, 3, rgb(255, 0, 0))
val pixels = engine.read_pixels()
val inside = pixels[3 * 10 + 3]
expect(color_r(inside)).to_equal(255)
expect(color_g(inside)).to_equal(0)
val outside = pixels[0 * 10 + 0]
expect(color_r(outside)).to_equal(0)
engine.shutdown()
```

</details>

#### clear fills entire framebuffer

- clear fills entire framebuffer
   - Expected: color_r(tl) equals `255`
   - Expected: color_g(tl) equals `0`
   - Expected: color_r(br) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear fills entire framebuffer")
var engine = Engine2D.create_with_backend(8, 8, "cpu")
engine.clear(rgb(255, 0, 0))
val pixels = engine.read_pixels()
val tl = pixels[0 * 8 + 0]
expect(color_r(tl)).to_equal(255)
expect(color_g(tl)).to_equal(0)
val br = pixels[7 * 8 + 7]
expect(color_r(br)).to_equal(255)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine2d_drawing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D Drawing Primitives.
- Engine2D Drawing Primitives

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d8b4a002195230ef2f2dbf5bbcf5f1fca25db5dc95853410a4cebf5b2d20abf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d8b4a002195230ef2f2dbf5bbcf5f1fca25db5dc95853410a4cebf5b2d20abf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d8b4a002195230ef2f2dbf5bbcf5f1fca25db5dc95853410a4cebf5b2d20abf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/rendering/engine2d_drawing_spec.spl
mirror: doc/06_spec/integration/rendering/engine2d_drawing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine2d_drawing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine2d_drawing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine2d_drawing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine2d_drawing_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw_rect_filled fills correct region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_drawing_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear fills entire framebuffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
