# Draw Quad Specification

> Tests covering SharedQuadState, DrawQuad::solid_color, DrawQuad::texture, DrawQuad::render_pass, DrawQuadKind.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Quad Specification

## Scenarios

### SharedQuadState

#### opacity is 1.0 when built with explicit value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opacity is 1.0 when built with explicit value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opacity is 1.0 when built with explicit value")
val sqs = _identity_sqs()
expect sqs.opacity to_equal 1.0
```

</details>

#### is_clipped defaults to false

- is_clipped defaults to false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_clipped defaults to false")
val sqs = _identity_sqs()
expect sqs.is_clipped to_equal false
```

</details>

### DrawQuad::solid_color

#### sets kind to SolidColor

- sets kind to SolidColor


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets kind to SolidColor")
val rect = _rect(0.0, 0.0, 50.0, 50.0)
val color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val q = DrawQuad.solid_color(0, rect, color)
val is_solid = match q.kind:
    DrawQuadKind.SolidColor: true
    _: false
expect is_solid to_equal true
```

</details>

#### carries the supplied color

- carries the supplied color


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries the supplied color")
val rect = _rect(0.0, 0.0, 50.0, 50.0)
val color = SkColor4f(r: 0.5, g: 0.2, b: 0.8, a: 1.0)
val q = DrawQuad.solid_color(0, rect, color)
expect q.solid_color.r to_equal 0.5
expect q.solid_color.g to_equal 0.2
```

</details>

#### rect and visible_rect are both set to constructor rect

- rect and visible_rect are both set to constructor rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rect and visible_rect are both set to constructor rect")
val rect = _rect(10.0, 20.0, 60.0, 80.0)
val color = SkColor4f(r: 0.0, g: 0.0, b: 0.0, a: 1.0)
val q = DrawQuad.solid_color(2, rect, color)
expect q.rect.left to_equal 10.0
expect q.visible_rect.top to_equal 20.0
```

</details>

### DrawQuad::texture

#### sets kind to Texture

- sets kind to Texture


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets kind to Texture")
val rect = _rect(0.0, 0.0, 100.0, 100.0)
val mailbox = SharedImageMailbox(bytes: [])
val q = DrawQuad.texture(0, rect, mailbox)
val is_tex = match q.kind:
    DrawQuadKind.Texture: true
    _: false
expect is_tex to_equal true
```

</details>

#### carries the mailbox

- carries the mailbox


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries the mailbox")
val rect = _rect(0.0, 0.0, 100.0, 100.0)
val mailbox = SharedImageMailbox(bytes: [1, 2, 3])
val q = DrawQuad.texture(0, rect, mailbox)
expect q.texture_mailbox.bytes.len() to_equal 3
```

</details>

### DrawQuad::render_pass

#### sets kind to RenderPass

- sets kind to RenderPass


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets kind to RenderPass")
val rect = _rect(0.0, 0.0, 800.0, 600.0)
val q = DrawQuad.render_pass(0, rect, 42)
val is_rp = match q.kind:
    DrawQuadKind.RenderPass: true
    _: false
expect is_rp to_equal true
```

</details>

#### carries the pass_id

- carries the pass_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("carries the pass_id")
val rect = _rect(0.0, 0.0, 800.0, 600.0)
val q = DrawQuad.render_pass(1, rect, 99)
expect q.render_pass_id to_equal 99
```

</details>

### DrawQuadKind

#### has 6 variants distinguishable by pattern match

- has 6 variants distinguishable by pattern match


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 6 variants distinguishable by pattern match")
val kinds: [DrawQuadKind] = [
    DrawQuadKind.SolidColor,
    DrawQuadKind.Texture,
    DrawQuadKind.Tile,
    DrawQuadKind.RenderPass,
    DrawQuadKind.Video,
    DrawQuadKind.Debug
]
expect kinds.len() to_equal 6
```

</details>

#### two quads with same sqs_index have distinct rects

- two quads with same sqs_index have distinct rects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two quads with same sqs_index have distinct rects")
val r1 = _rect(0.0, 0.0, 10.0, 10.0)
val r2 = _rect(20.0, 20.0, 30.0, 30.0)
val color = SkColor4f(r: 0.0, g: 0.0, b: 0.0, a: 1.0)
val q1 = DrawQuad.solid_color(0, r1, color)
val q2 = DrawQuad.solid_color(0, r2, color)
expect q1.rect.left to_equal 0.0
expect q2.rect.left to_equal 20.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/viz/draw_quad_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SharedQuadState, DrawQuad::solid_color, DrawQuad::texture, DrawQuad::render_pass, DrawQuadKind.
- SharedQuadState
- DrawQuad::solid_color
- DrawQuad::texture
- DrawQuad::render_pass
- DrawQuadKind

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `6221d4e9cc625f168ca8b5557b48fd74cac9c14f27af9c90bec0c47d1cd20a26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6221d4e9cc625f168ca8b5557b48fd74cac9c14f27af9c90bec0c47d1cd20a26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6221d4e9cc625f168ca8b5557b48fd74cac9c14f27af9c90bec0c47d1cd20a26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/viz/draw_quad_spec.spl
mirror: doc/06_spec/unit/lib/viz/draw_quad_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/viz/draw_quad_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/viz/draw_quad_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/viz/draw_quad_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opacity is 1.0 when built with explicit value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/draw_quad_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_clipped defaults to false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/draw_quad_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets kind to SolidColor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
