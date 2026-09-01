# Scene To Canvas2d Json Specification

> Tests covering render_scene_to_canvas2d_ops.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scene To Canvas2d Json Specification

## Scenarios

### render_scene_to_canvas2d_ops

#### serializes basic scene commands for the hosted canvas shell

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serializes basic scene commands for the hosted canvas shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes basic scene commands for the hosted canvas shell")
val scene = render_scene(
    [
        scene_fill_rect(4, 6, 20, 12, 0xFFFF0000),
        scene_text(10, 24, "Hello", 0xFF112233, 14),
        scene_clip_push(0, 0, 40, 30),
        scene_clip_pop()
    ],
    80,
    60
)

val json = render_scene_to_canvas2d_ops(scene)
expect(json).to_contain("\"op\":\"fillRect\"")
expect(json).to_contain("\"text\":\"Hello\"")
expect(json).to_contain("\"op\":\"pushClip\"")
expect(json).to_contain("\"op\":\"popClip\"")
```

</details>

#### applies offsets when translating scene output

- applies offsets when translating scene output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies offsets when translating scene output")
val scene = render_scene([scene_fill_rect(2, 3, 8, 9, 0xFF00FF00)], 32, 24)
val json = render_scene_to_canvas2d_ops_with_offset(scene, 10, 20)

expect(json).to_contain("\"x\":12")
expect(json).to_contain("\"y\":23")
```

</details>

#### serializes primitive placement and high-dpi scale for mobile canvas shells

- serializes primitive placement and high-dpi scale for mobile canvas shells


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes primitive placement and high-dpi scale for mobile canvas shells")
val scene = render_scene(
    [
        scene_stroke_rect(1, 2, 10, 11, 0xFF010203, 2),
        scene_line(3, 4, 13, 14, 0xFF102030, 1),
        scene_circle_filled(5, 6, 7, 0xFFABCDEF),
        scene_rounded_rect(8, 9, 20, 21, 0xFF445566, 4),
        scene_gradient_rect(10, 12, 30, 40, 0xFF000000, 0xFFFFFFFF)
    ],
    100,
    50
)

val json = render_scene_to_canvas2d_ops_with_offset_and_scale(scene, 1, 2, 2)
expect(json).to_contain("\"width\":200")
expect(json).to_contain("\"height\":100")
expect(json).to_contain("\"devicePixelRatio\":2")
expect(json).to_contain("\"op\":\"strokeRect\"")
expect(json).to_contain("\"strokeWidth\":4")
expect(json).to_contain("\"op\":\"line\"")
expect(json).to_contain("\"x2\":28")
expect(json).to_contain("\"op\":\"circle\"")
expect(json).to_contain("\"filled\":true")
expect(json).to_contain("\"op\":\"roundRect\"")
expect(json).to_contain("\"radius\":8")
expect(json).to_contain("\"op\":\"linearGradientRect\"")
```

</details>

#### serializes image bounds and escapes text content

- serializes image bounds and escapes text content


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes image bounds and escapes text content")
val scene = render_scene(
    [
        scene_text(1, 2, "Hello \"Canvas\"\nWorld", 0xFF222222, 16),
        scene_image(4, 5, 20, 10, [0xFF000000, 0xFFFFFFFF], 2, 1)
    ],
    64,
    32
)

val json = render_scene_to_canvas2d_ops(scene)
expect(json).to_contain("Hello \\\"Canvas\\\"\\nWorld")
expect(json).to_contain("\"op\":\"drawImage\"")
expect(json).to_contain("\"pixelWidth\":2")
expect(json).to_contain("\"pixelHeight\":1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering render_scene_to_canvas2d_ops.
- render_scene_to_canvas2d_ops

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b8d8dced37612541b6e22a32f321bb7523fcfb9493b36c6f7e0c431913527a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b8d8dced37612541b6e22a32f321bb7523fcfb9493b36c6f7e0c431913527a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b8d8dced37612541b6e22a32f321bb7523fcfb9493b36c6f7e0c431913527a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.spl
mirror: doc/06_spec/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes basic scene commands for the hosted canvas shell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies offsets when translating scene output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/render_scene/scene_to_canvas2d_json_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes primitive placement and high-dpi scale for mobile canvas shells' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
