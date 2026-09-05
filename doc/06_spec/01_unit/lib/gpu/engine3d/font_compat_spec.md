# Font Compat Specification

> Tests covering Engine3D font compatibility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Compat Specification

## Scenarios

### Engine3D font compatibility

#### keeps one font execution target for each frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps one font execution target for each frame
   - Expected: engine3d_font_completion_target(true, 1) equals `vulkan`
   - Expected: engine3d_font_completion_target(false, 1) equals `cpu`
   - Expected: engine3d_font_completion_target(false, 0) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps one font execution target for each frame")
expect(engine3d_font_frame_target_allows("", "cpu")).to_be(true)
expect(engine3d_font_frame_target_allows("cpu", "cpu")).to_be(true)
expect(engine3d_font_frame_target_allows("vulkan", "vulkan")).to_be(true)
expect(engine3d_font_frame_target_allows("cpu", "vulkan")).to_be(false)
expect(engine3d_font_frame_target_allows("vulkan", "cpu")).to_be(false)
expect(engine3d_font_completion_target(true, 1)).to_equal("vulkan")
expect(engine3d_font_completion_target(false, 1)).to_equal("cpu")
expect(engine3d_font_completion_target(false, 0)).to_equal("unavailable")
```

</details>

#### falls back by policy and leaves invalid configuration state untouched

- falls back by policy and leaves invalid configuration state untouched
   - Expected: engine.font_execution_attempts() equals `["vulkan:unavailable", "cpu:success"]`
   - Expected: engine.font_execution_target() equals `cpu`
   - Expected: engine.font_execution_attempts() equals `["vulkan:frame-target=cpu"]`
   - Expected: engine.font_execution_attempts() equals `["vulkan:unavailable"]`
   - Expected: after_stats.entries equals `before_stats.entries`
   - Expected: after_stats.hits equals `before_stats.hits`
   - Expected: after_stats.misses equals `before_stats.misses`
   - Expected: engine.font_execution_attempts() equals `before_attempts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back by policy and leaves invalid configuration state untouched")
var engine = Engine3D.create_with_backend(64, 48, "cpu")
engine.clear(0u32)
engine.begin_frame()
expect(engine.draw_text_hud_configured(
    4, 4, "A", 0xffffffffu32, _font_config("vulkan", FontExecutionPolicy.Suggested)
)).to_be(true)
expect(engine.font_execution_attempts()).to_equal(["vulkan:unavailable", "cpu:success"])
expect(engine.font_execution_target()).to_equal("cpu")
expect(engine.draw_text_hud_configured(
    4, 4, "A", 0xffffffffu32, _font_config("vulkan", FontExecutionPolicy.Required)
)).to_be(false)
expect(engine.font_execution_attempts()).to_equal(["vulkan:frame-target=cpu"])
engine.end_frame()
engine.begin_frame()
expect(engine.draw_text_hud_configured(
    4, 4, "A", 0xffffffffu32, _font_config("vulkan", FontExecutionPolicy.Required)
)).to_be(false)
expect(engine.font_execution_attempts()).to_equal(["vulkan:unavailable"])
val before_stats = engine.font_cache_stats()
val before_attempts = engine.font_execution_attempts()
expect(engine.draw_text_hud_configured(
    4, 4, "B", 0xffffffffu32, _font_config("auto", FontExecutionPolicy.Preferred)
)).to_be(false)
val after_stats = engine.font_cache_stats()
expect(after_stats.entries).to_equal(before_stats.entries)
expect(after_stats.hits).to_equal(before_stats.hits)
expect(after_stats.misses).to_equal(before_stats.misses)
expect(engine.font_execution_attempts()).to_equal(before_attempts)
engine.end_frame()
engine.shutdown()
```

</details>

#### draws live neutral glyph runs and rejects malformed or stale material

- draws live neutral glyph runs and rejects malformed or stale material


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draws live neutral glyph runs and rejects malformed or stale material")
val loaded = load_font("src/compiler_rust/vendor/ttf-parser/tests/fonts/demo.ttf")
expect(loaded).to_not_be_nil()
val face = loaded as std.nogc_sync_mut.io.font_sffi.FontHandle
val glyph_id = glyph_index(face, 65)
expect(glyph_id).to_be_greater_than(0)
val run = FontGlyphRun(valid: true, face_id: face.handle, face_generation: face.generation,
    glyph_ids: [glyph_id.to_u32()], xs: [0], ys: [0], clusters: [0])
val malformed = FontGlyphRun(valid: true, face_id: face.handle, face_generation: face.generation,
    glyph_ids: [glyph_id.to_u32()], xs: [], ys: [0], clusters: [0])
val wrong_face = FontGlyphRun(valid: true, face_id: face.handle + 1, face_generation: face.generation,
    glyph_ids: [glyph_id.to_u32()], xs: [0], ys: [0], clusters: [0])
val negative_cluster = FontGlyphRun(valid: true, face_id: face.handle, face_generation: face.generation,
    glyph_ids: [glyph_id.to_u32()], xs: [0], ys: [0], clusters: [-1])

var engine = Engine3D.create_with_backend(64, 64, "cpu")
engine.clear(0u32)
expect(engine.draw_glyph_run_hud(4, 4, run, 0xFFFFFFFFu32, 14)).to_be(true)
expect(engine.draw_glyph_run_hud(4, 4, malformed, 0xFFFFFFFFu32, 14)).to_be(false)
expect(engine.draw_glyph_run_hud(4, 4, wrong_face, 0xFFFFFFFFu32, 14)).to_be(false)
expect(engine.draw_glyph_run_hud(4, 4, negative_cluster, 0xFFFFFFFFu32, 14)).to_be(false)
engine.set_camera(mat4_identity(), mat4_perspective(1.0, 1.0, 0.1, 100.0))
expect(engine.draw_glyph_run_world(0.0, 0.0, -1.0, run, 0xFF00FF00u32, 12)).to_be(true)
expect(engine.draw_glyph_run_world(0.0, 0.0, 1.0, run, 0xFF00FF00u32, 12)).to_be(false)
expect(_any_font_pixel(engine.read_pixels())).to_be(true)

free_font(face)
expect(engine.draw_glyph_run_hud(4, 4, run, 0xFFFFFFFFu32, 14)).to_be(false)
engine.shutdown()
```

</details>

#### draws prepared font material through the CPU HUD fallback

- draws prepared font material through the CPU HUD fallback
   - Expected: engine.backend_name() equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draws prepared font material through the CPU HUD fallback")
var engine = Engine3D.create_with_backend(64, 48, "cpu")
engine.clear(0u32)
expect(engine.draw_text_hud(4, 4, "A", 0xFFFFFFFFu32, 14)).to_be(true)
expect(_any_font_pixel(engine.read_pixels())).to_be(true)
expect(engine.font_cache_stats().misses).to_be_greater_than(0)
expect(engine.backend_name()).to_equal("cpu")
engine.shutdown()
```

</details>

#### rejects empty and offscreen HUD runs without changing the backend

- rejects empty and offscreen HUD runs without changing the backend
   - Expected: engine.backend_name() equals `cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty and offscreen HUD runs without changing the backend")
var engine = Engine3D.create_with_backend(32, 24, "metal")
expect(engine.load_font("")).to_be(false)
expect(engine.draw_text_hud(0, 0, "", 0xFFFFFFFFu32, 12)).to_be(false)
expect(engine.draw_text_hud(100, 100, "A", 0xFFFFFFFFu32, 12)).to_be(false)
expect(engine.backend_name()).to_equal("cpu")
engine.unload_font()
engine.shutdown()
```

</details>

#### preserves the scene beneath transparent glyph padding

- preserves the scene beneath transparent glyph padding
   - Expected: rendered[oracle_index] equals `oracle_pixel`
   - Expected: rendered[padding_index] equals `background`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves the scene beneath transparent glyph padding")
val background = 0xFF112233u32
val color = 0x80402010u32
var oracle = FontRenderer.new()
val batch = oracle.prepare_text("A", color, 14)
expect(batch.valid).to_be(true)
expect(batch.quads.len()).to_be_greater_than(0)
val quad = batch.quads[0]
var oracle_index = -1
var oracle_pixel = 0u32
var padding_index = -1
var row = 0
while row < quad.height:
    var col = 0
    while col < quad.width:
        val atlas_alpha = (batch.atlas_pixels[(quad.atlas_y + row) * batch.atlas_width + quad.atlas_x + col] >> 24) & 0xFFu32
        if atlas_alpha > 0u32 and oracle_index < 0:
            val effective_alpha = (atlas_alpha * ((color >> 24) & 0xFFu32) + 127u32) / 255u32
            val source = (effective_alpha << 24) | (color & 0x00FFFFFFu32)
            oracle_index = (2 + quad.dst_y + row) * 32 + 2 + quad.dst_x + col
            oracle_pixel = blend3d(source, background)
        if atlas_alpha == 0u32 and padding_index < 0:
            padding_index = (2 + quad.dst_y + row) * 32 + 2 + quad.dst_x + col
        col = col + 1
    row = row + 1
expect(oracle_index).to_be_greater_than(-1)
expect(padding_index).to_be_greater_than(-1)

var engine = Engine3D.create_with_backend(32, 24, "cpu")
engine.clear(background)
expect(engine.draw_text_hud(2, 2, "A", color, 14)).to_be(true)
val rendered = engine.read_pixels()
expect(rendered[oracle_index]).to_equal(oracle_pixel)
expect(rendered[padding_index]).to_equal(background)
engine.shutdown()
```

</details>

#### projects visible world text and rejects behind or outside points

- projects visible world text and rejects behind or outside points


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects visible world text and rejects behind or outside points")
var engine = Engine3D.create_with_backend(64, 64, "cpu")
engine.clear(0u32)
engine.set_camera(mat4_identity(), mat4_perspective(1.0, 1.0, 0.1, 100.0))
expect(engine.draw_text_world(0.0, 0.0, -1.0, "A", 0xFF00FF00u32, 12)).to_be(true)
expect(engine.draw_text_world(0.0, 0.0, 1.0, "A", 0xFF00FF00u32, 12)).to_be(false)
expect(engine.draw_text_world(100.0, 0.0, -1.0, "A", 0xFF00FF00u32, 12)).to_be(false)
expect(_any_font_pixel(engine.read_pixels())).to_be(true)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/font_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine3D font compatibility.
- Engine3D font compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `259153d8305d0f6fe95648d3e1564e38ec2911764d46f7195b52134a78ef8525`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `259153d8305d0f6fe95648d3e1564e38ec2911764d46f7195b52134a78ef8525`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `259153d8305d0f6fe95648d3e1564e38ec2911764d46f7195b52134a78ef8525`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine3d/font_compat_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine3d/font_compat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine3d/font_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine3d/font_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine3d/font_compat_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps one font execution target for each frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine3d/font_compat_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back by policy and leaves invalid configuration state untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine3d/font_compat_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draws live neutral glyph runs and rejects malformed or stale material' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
