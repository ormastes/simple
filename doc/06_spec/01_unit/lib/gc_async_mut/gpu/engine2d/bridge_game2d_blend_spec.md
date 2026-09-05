# Bridge Game2d Blend Specification

> Tests covering Game2D bridge blend-mode wiring, Alpha blend mode, Multiply blend mode, Additive blend mode, Opaque blend mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bridge Game2d Blend Specification

## Scenarios

### Game2D bridge blend-mode wiring

### Alpha blend mode

#### draws white sprite with src-over compositing

- draws white sprite with src-over compositing


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draws white sprite with src-over compositing")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(EngineColor(r: 0.0, g: 0.0, b: 0.0, a: 1.0)))
val white_tint = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val dst_rect = Rect2(x: 10.0, y: 10.0, width: 50.0, height: 50.0)
val src_rect = Rect2(x: 0.0, y: 0.0, width: 50.0, height: 50.0)
buf.push(RenderCommand.DrawSprite(
    texture_id: TextureId(raw: 0),
    src_rect: src_rect,
    dst_rect: dst_rect,
    tint: white_tint,
    z_order: ZIndex(value: 0),
    blend_mode: BlendMode.Alpha))

val result = game2d_render_commands_on_engine2d(buf, 100, 100, "cpu_simd")
val pixel = result[10 * 100 + 10]
val (r, g, b, a) = rgba_unpack(pixel)
assert_eq(r, 255, "sprite pixel r should be 255")
assert_eq(g, 255, "sprite pixel g should be 255")
assert_eq(b, 255, "sprite pixel b should be 255")
```

</details>

#### leaves background untouched outside sprite

- leaves background untouched outside sprite


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves background untouched outside sprite")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(EngineColor(r: 0.0, g: 0.0, b: 0.0, a: 1.0)))
val white_tint = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val dst_rect = Rect2(x: 10.0, y: 10.0, width: 50.0, height: 50.0)
val src_rect = Rect2(x: 0.0, y: 0.0, width: 50.0, height: 50.0)
buf.push(RenderCommand.DrawSprite(
    texture_id: TextureId(raw: 0),
    src_rect: src_rect,
    dst_rect: dst_rect,
    tint: white_tint,
    z_order: ZIndex(value: 0),
    blend_mode: BlendMode.Alpha))

val result = game2d_render_commands_on_engine2d(buf, 100, 100, "cpu_simd")
val pixel_outside = result[5 * 100 + 5]
val (r, g, b, a) = rgba_unpack(pixel_outside)
assert_eq(r, 0, "background r should be 0")
assert_eq(g, 0, "background g should be 0")
assert_eq(b, 0, "background b should be 0")
```

</details>

### Multiply blend mode

#### produces multiplicative blending of red over white

- produces multiplicative blending of red over white


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces multiplicative blending of red over white")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)))
val red_tint = EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val dst_rect = Rect2(x: 10.0, y: 10.0, width: 50.0, height: 50.0)
val src_rect = Rect2(x: 0.0, y: 0.0, width: 50.0, height: 50.0)
buf.push(RenderCommand.DrawSprite(
    texture_id: TextureId(raw: 0),
    src_rect: src_rect,
    dst_rect: dst_rect,
    tint: red_tint,
    z_order: ZIndex(value: 0),
    blend_mode: BlendMode.Multiply))

val result = game2d_render_commands_on_engine2d(buf, 100, 100, "cpu_simd")
val pixel = result[10 * 100 + 10]
val (r, g, b, a) = rgba_unpack(pixel)
assert_eq(r, 255, "multiply: r should be 255")
assert_eq(g, 0, "multiply: g should be 0")
assert_eq(b, 0, "multiply: b should be 0")
```

</details>

### Additive blend mode

#### produces clamped additive blending of grey over grey

- produces clamped additive blending of grey over grey


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces clamped additive blending of grey over grey")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(EngineColor(r: 0.5, g: 0.5, b: 0.5, a: 1.0)))
val grey_tint = EngineColor(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val dst_rect = Rect2(x: 10.0, y: 10.0, width: 50.0, height: 50.0)
val src_rect = Rect2(x: 0.0, y: 0.0, width: 50.0, height: 50.0)
buf.push(RenderCommand.DrawSprite(
    texture_id: TextureId(raw: 0),
    src_rect: src_rect,
    dst_rect: dst_rect,
    tint: grey_tint,
    z_order: ZIndex(value: 0),
    blend_mode: BlendMode.Additive))

val result = game2d_render_commands_on_engine2d(buf, 100, 100, "cpu_simd")
val pixel = result[10 * 100 + 10]
val (r, g, b, a) = rgba_unpack(pixel)
# Additive is a CLAMPED SUM, not screen: 128 + 128 = 256 -> 255.
# Screen would give ~192 here; asserting 255 is what distinguishes
# true additive from the screen substitution.
assert_true(r >= 254, "additive r should clamp to 255")
assert_true(g >= 254, "additive g should clamp to 255")
assert_true(b >= 254, "additive b should clamp to 255")
```

</details>

### Opaque blend mode

#### behaves like Alpha (src-over)

- behaves like Alpha (src-over)


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("behaves like Alpha (src-over)")
var buf = RenderCommandBuffer.create()
buf.push(RenderCommand.Clear(EngineColor(r: 0.0, g: 0.0, b: 0.0, a: 1.0)))
val white_tint = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val dst_rect = Rect2(x: 10.0, y: 10.0, width: 50.0, height: 50.0)
val src_rect = Rect2(x: 0.0, y: 0.0, width: 50.0, height: 50.0)
buf.push(RenderCommand.DrawSprite(
    texture_id: TextureId(raw: 0),
    src_rect: src_rect,
    dst_rect: dst_rect,
    tint: white_tint,
    z_order: ZIndex(value: 0),
    blend_mode: BlendMode.Opaque))

val result = game2d_render_commands_on_engine2d(buf, 100, 100, "cpu_simd")
val pixel = result[10 * 100 + 10]
val (r, g, b, a) = rgba_unpack(pixel)
assert_eq(r, 255, "opaque r should be 255")
assert_eq(g, 255, "opaque g should be 255")
assert_eq(b, 255, "opaque b should be 255")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Game2D bridge blend-mode wiring, Alpha blend mode, Multiply blend mode, Additive blend mode, Opaque blend mode.
- Game2D bridge blend-mode wiring
- Alpha blend mode
- Multiply blend mode
- Additive blend mode
- Opaque blend mode

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4b2b04ceac370aa3ec3b5212649026ab4d553f57b01e55030a92e13df19b684b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b2b04ceac370aa3ec3b5212649026ab4d553f57b01e55030a92e13df19b684b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b2b04ceac370aa3ec3b5212649026ab4d553f57b01e55030a92e13df19b684b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draws white sprite with src-over compositing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves background untouched outside sprite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/bridge_game2d_blend_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces multiplicative blending of red over white' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
