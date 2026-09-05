# Engine2d Mask Specification

> Tests covering Engine2D Stencil Mask.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Mask Specification

## Scenarios

### Engine2D Stencil Mask

#### cpu backend

#### set_mask blocks draws in masked region

- set_mask blocks draws in masked region
   - Expected: color_r(p_left) equals `0`
   - Expected: color_r(p_right) equals `255`
   - Expected: color_g(p_right) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("set_mask blocks draws in masked region")
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))

val mask = _make_right_half_mask()
engine.set_mask(mask, 10, 10)
engine.draw_rect_filled(0, 0, 10, 10, rgb(255, 0, 0))

val pixels = engine.read_pixels()
val p_left = pixels[0 * 10 + 2]
expect(color_r(p_left)).to_equal(0)
val p_right = pixels[0 * 10 + 7]
expect(color_r(p_right)).to_equal(255)
expect(color_g(p_right)).to_equal(0)
engine.shutdown()
```

</details>

#### clear_mask removes clipping

- clear_mask removes clipping
   - Expected: color_r(p1) equals `0`
   - Expected: color_g(p2) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear_mask removes clipping")
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))

val mask = _make_block_all_mask()
engine.set_mask(mask, 10, 10)
engine.draw_rect_filled(0, 0, 10, 10, rgb(255, 0, 0))

val p1 = engine.read_pixels()[55]
expect(color_r(p1)).to_equal(0)

engine.clear_mask()
engine.draw_rect_filled(0, 0, 10, 10, rgb(0, 255, 0))

val p2 = engine.read_pixels()[55]
expect(color_g(p2)).to_equal(255)
engine.shutdown()
```

</details>

#### mask does not affect clear

- mask does not affect clear
   - Expected: color_b(p) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mask does not affect clear")
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(255, 0, 0))

val mask = _make_block_all_mask()
engine.set_mask(mask, 10, 10)

engine.clear(rgb(0, 0, 255))
val pixels = engine.read_pixels()
val p = pixels[0]
expect(color_b(p)).to_equal(255)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine2d_mask_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D Stencil Mask.
- Engine2D Stencil Mask

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

- Canonical SPipe generation for source `f5b2fb0f8fb3eb61e1234cad5837c4486dc16c0c2f187b9d84bc44ea6e7bed33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5b2fb0f8fb3eb61e1234cad5837c4486dc16c0c2f187b9d84bc44ea6e7bed33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5b2fb0f8fb3eb61e1234cad5837c4486dc16c0c2f187b9d84bc44ea6e7bed33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/engine2d_mask_spec.spl
mirror: doc/06_spec/integration/rendering/engine2d_mask_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine2d_mask_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine2d_mask_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine2d_mask_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine2d_mask_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'set_mask blocks draws in masked region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_mask_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear_mask removes clipping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_mask_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mask does not affect clear' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
