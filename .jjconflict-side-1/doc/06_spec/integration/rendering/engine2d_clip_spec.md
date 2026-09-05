# Engine2d Clip Specification

> Tests covering Engine2D Clipping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Clip Specification

## Scenarios

### Engine2D Clipping

#### cpu backend

#### set_clip restricts draw_rect_filled

- set_clip restricts draw_rect_filled
   - Expected: color_r(outside) equals `0`
   - Expected: color_r(inside) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("set_clip restricts draw_rect_filled")
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))
engine.set_clip(5, 5, 5, 5)
engine.draw_rect_filled(0, 0, 10, 10, rgb(255, 0, 0))
val pixels = engine.read_pixels()
val outside = pixels[2 * 10 + 2]
expect(color_r(outside)).to_equal(0)
val inside = pixels[7 * 10 + 7]
expect(color_r(inside)).to_equal(255)
engine.shutdown()
```

</details>

#### clear_clip restores full drawing area

- clear_clip restores full drawing area
   - Expected: color_g(p) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear_clip restores full drawing area")
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.clear(rgb(0, 0, 0))
engine.set_clip(5, 5, 5, 5)
engine.clear_clip()
engine.draw_rect_filled(0, 0, 10, 10, rgb(0, 255, 0))
val pixels = engine.read_pixels()
val p = pixels[2 * 10 + 2]
expect(color_g(p)).to_equal(255)
engine.shutdown()
```

</details>

#### clip does not affect clear

- clip does not affect clear
   - Expected: color_b(p) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip does not affect clear")
var engine = Engine2D.create_with_backend(10, 10, "cpu")
engine.set_clip(5, 5, 5, 5)
engine.clear(rgb(0, 0, 255))
val pixels = engine.read_pixels()
val p = pixels[2 * 10 + 2]
expect(color_b(p)).to_equal(255)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine2d_clip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D Clipping.
- Engine2D Clipping

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

- Canonical SPipe generation for source `f3e9f2851711b175af278159c9897e93cd0e01490c727e1c26590c4e68192047`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3e9f2851711b175af278159c9897e93cd0e01490c727e1c26590c4e68192047`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3e9f2851711b175af278159c9897e93cd0e01490c727e1c26590c4e68192047`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/engine2d_clip_spec.spl
mirror: doc/06_spec/integration/rendering/engine2d_clip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine2d_clip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine2d_clip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine2d_clip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine2d_clip_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'set_clip restricts draw_rect_filled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_clip_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear_clip restores full drawing area' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_clip_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clip does not affect clear' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
