# Engine3d Drawing Specification

> Tests covering Engine3D Drawing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine3d Drawing Specification

## Scenarios

### Engine3D Drawing

#### cpu backend

#### clear fills framebuffer with color

- clear fills framebuffer with color
   - Expected: color3d_r(p) equals `255`
   - Expected: color3d_g(p) equals `0`
   - Expected: color3d_b(p) equals `0`
   - Expected: color3d_r(p2) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear fills framebuffer with color")
var engine = Engine3D.create_with_backend(8, 8, "cpu")
engine.begin_frame()
engine.clear(0xFFFF0000)
engine.end_frame()
val pixels = engine.read_pixels()
val p = pixels[0]
expect(color3d_r(p)).to_equal(255)
expect(color3d_g(p)).to_equal(0)
expect(color3d_b(p)).to_equal(0)
val p2 = pixels[63]
expect(color3d_r(p2)).to_equal(255)
engine.shutdown()
```

</details>

#### clear_depth resets depth buffer

- clear_depth resets depth buffer
   - Expected: (depth[0] as i32) equals `1`
   - Expected: (depth[15] as i32) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear_depth resets depth buffer")
var engine = Engine3D.create_with_backend(4, 4, "cpu")
engine.begin_frame()
engine.clear_depth()
engine.end_frame()
val depth = engine.read_depth()
expect((depth[0] as i32)).to_equal(1)
expect((depth[15] as i32)).to_equal(1)
engine.shutdown()
```

</details>

#### submit_triangle renders a triangle

- submit_triangle renders a triangle
   - Expected: color3d_r(center) equals `255`
   - Expected: color3d_g(center) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("submit_triangle renders a triangle")
var engine = Engine3D.create_with_backend(10, 10, "cpu")
engine.begin_frame()
engine.clear(0xFF000000)
engine.clear_depth()
engine.set_depth_test(false)
engine.set_cull_mode(0)
val view = mat4_look_at(0.0, 0.0, 5.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
val proj = mat4_perspective(1.0, 1.0, 0.1, 100.0)
engine.set_camera(view, proj)
val v0 = vertex3d_pos_color(0.0, 1.0, 0.0, 0xFFFF0000)
val v1 = vertex3d_pos_color(-1.0, -1.0, 0.0, 0xFFFF0000)
val v2 = vertex3d_pos_color(1.0, -1.0, 0.0, 0xFFFF0000)
val mat = material_unlit(0xFFFF0000)
val model = mat4_identity()
engine.submit_triangle(v0, v1, v2, mat, model)
engine.end_frame()
val pixels = engine.read_pixels()
# Center pixel (5,5) should be red (inside triangle)
val center = pixels[5 * 10 + 5]
expect(color3d_r(center)).to_equal(255)
expect(color3d_g(center)).to_equal(0)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine3d_drawing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine3D Drawing.
- Engine3D Drawing

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

- Canonical SPipe generation for source `b386577349a327bc420eff79e6d828313b0a65b5aed5571d5646ed01a67c6da8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b386577349a327bc420eff79e6d828313b0a65b5aed5571d5646ed01a67c6da8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b386577349a327bc420eff79e6d828313b0a65b5aed5571d5646ed01a67c6da8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/engine3d_drawing_spec.spl
mirror: doc/06_spec/integration/rendering/engine3d_drawing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine3d_drawing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine3d_drawing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine3d_drawing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine3d_drawing_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear fills framebuffer with color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine3d_drawing_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear_depth resets depth buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine3d_drawing_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'submit_triangle renders a triangle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
