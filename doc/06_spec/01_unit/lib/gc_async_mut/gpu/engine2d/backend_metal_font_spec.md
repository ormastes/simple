# Metal Font Atlas Companion Specification

> Manually synchronized on 2026-07-12; no Simple/docgen or native Metal command
> ran in this session.

Seven scenarios verify the exact 13-word/52-byte little-endian parameter block,
signed-coordinate overflow rejection, the initial invalidated atlas state,
sequential distinct-renderer dependency tokens do not alias cached Metal atlas
state under serialized access,
unsupported program versions fail before atlas mutation, failed zero-prefix
preservation of device framebuffer truth, and native-only typed Metal routing.
Runtime upload, pipeline, and device-readback acceptance remain macOS
integration evidence. Concurrent token allocation and renderer ownership remain
unsupported.

<details>
<summary>Full Scenario Manual</summary>

# Backend Metal Font Specification

## Scenarios

### Metal font atlas companion

#### packs the frozen 13-word ABI into 52 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- packs the frozen 13-word ABI into 52 bytes
   - Expected: METAL_FONT_PARAMS_BYTES equals `52`
   - Expected: p.len() equals `52`
   - Expected: p[0] equals `1`
   - Expected: p[40] equals `0xF5`
   - Expected: p[43] equals `0xFF`
   - Expected: p[48] equals `0xDD`
   - Expected: p[51] equals `0xAA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("packs the frozen 13-word ABI into 52 bytes")
expect(METAL_FONT_PARAMS_BYTES).to_equal(52)
val p = metal_font_atlas_composite_params(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, -11, -12, 0xAABBCCDDu32)
expect(p.len()).to_equal(52)
expect(p[0]).to_equal(1)
expect(p[40]).to_equal(0xF5)
expect(p[43]).to_equal(0xFF)
expect(p[48]).to_equal(0xDD)
expect(p[51]).to_equal(0xAA)
```

</details>

#### keeps Metal's frozen 52-byte ABI behind overflow-safe source guards

- keeps Metal's frozen 52-byte ABI behind overflow-safe source guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps Metal's frozen 52-byte ABI behind overflow-safe source guards")
val source = font_atlas_composite_metal_source()
expect(source).to_contain("uint color;\n};\n\nkernel void simple_font_atlas_composite_v1_u32")
expect(source).to_contain("p.atlas_width == 0u || p.atlas_height == 0u")
expect(source).to_contain("p.atlas_width > 2147483647u || p.atlas_height > 2147483647u")
expect(source).to_contain("p.atlas_width > 0xffffffffu / p.atlas_height")
expect(source).to_contain("p.atlas_count != p.atlas_width * p.atlas_height")
expect(source).to_contain("p.dst_count != p.dst_width * p.dst_height")
expect(source).to_contain("p.dst_x > 2147483647 - int(local_x)")
expect(source).to_contain("p.dst_y > 2147483647 - int(local_y)")
```

</details>

#### starts atlas state invalidated

- starts atlas state invalidated
   - Expected: state.atlas_generation equals `-1`
   - Expected: state.atlas_owner_identity equals ``
   - Expected: state.atlas_buffer equals `0`
   - Expected: state.font_artifact_sha256 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts atlas state invalidated")
val state = MetalFontBackendState.create()
expect(state.atlas_generation).to_equal(-1)
expect(state.atlas_owner_identity).to_equal("")
expect(state.atlas_buffer).to_equal(0)
expect(state.font_artifact_sha256).to_equal("")
```

</details>

#### invalidates the Metal atlas owner with its generation

- invalidates the Metal atlas owner with its generation
   - Expected: state.atlas_generation equals `-1`
   - Expected: state.atlas_owner_identity equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invalidates the Metal atlas owner with its generation")
var state = MetalFontBackendState.create()
state.atlas_generation = 7
state.atlas_owner_identity = "owner"
state.invalidate()
expect(state.atlas_generation).to_equal(-1)
expect(state.atlas_owner_identity).to_equal("")
```

</details>

#### requires generation and owner identity for a Metal atlas cache hit

- requires generation and owner identity for a Metal atlas cache hit
   - Expected: source.index_of("if (self.font_artifact_sha256 == \"\"") < source.index_of("sha256_text(font_atlas_composite_metal_source())") is true
   - Expected: source.split("sha256_text(font_atlas_composite_metal_source())").len() equals `2`
   - Expected: source does not contain `val artifact_identity = if session.font_shader_lib > 0 and session.pipe_font_... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires generation and owner identity for a Metal atlas cache hit")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_metal_font.spl")
expect(source).to_contain("font_atlas_composite_cache_identity(")
expect(source).to_contain("font_render_batch_atlas_owner_identity(batch), \"metal\", device_features")
expect(source).to_contain("if (self.font_artifact_sha256 == \"\" and session.font_shader_lib > 0")
expect(source.index_of("if (self.font_artifact_sha256 == \"\"") < source.index_of("sha256_text(font_atlas_composite_metal_source())")).to_equal(true)
expect(source.split("sha256_text(font_atlas_composite_metal_source())").len()).to_equal(2)
expect(source).to_contain("\"source-sha256=\" + self.font_artifact_sha256")
expect(source).to_contain("artifact_identity, dependency_identity")
expect(source).to_contain("self.font_artifact_sha256 = \"\"")
expect(source.contains("val artifact_identity = if session.font_shader_lib > 0 and session.pipe_font_atlas_composite > 0:\n            \"library=\"")).to_equal(false)
expect(source).to_contain("self.atlas_generation == batch.atlas_generation and self.atlas_owner_identity == owner_identity")
expect(source).to_contain("self.atlas_owner_identity = owner_identity")
```

</details>

#### keeps sequential distinct-renderer tokens from aliasing Metal cache state

- keeps sequential distinct-renderer tokens from aliasing Metal cache state
   - Expected: first.is_empty() is false
   - Expected: second.is_empty() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps sequential distinct-renderer tokens from aliasing Metal cache state")
var first_renderer = FontRenderer.new()
var second_renderer = FontRenderer.new()
val first = first_renderer.prepare_text("A", 0xffffffffu32, 16)
val second = second_renderer.prepare_text("B", 0xffffffffu32, 16)
var state = MetalFontBackendState.create()
state.atlas_generation = first.atlas_generation

expect(first.is_empty()).to_equal(false)
expect(second.is_empty()).to_equal(false)
expect(first.atlas_generation).to_be_greater_than(0)
expect(second.atlas_generation).to_be_greater_than(0)
assert_not_equal(state.atlas_generation, second.atlas_generation)
```

</details>

#### rejects destination coordinate overflow before ABI packing

- rejects destination coordinate overflow before ABI packing
   - Expected: font_destination_origin(10, -3, 1).? equals `7`
   - Expected: font_destination_origin(2147483647, 0, 1).? equals `2147483647`
   - Expected: font_destination_origin(-2147483648, 0, 2).? equals `-2147483648`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects destination coordinate overflow before ABI packing")
expect(font_destination_origin(10, -3, 1).?).to_equal(7)
expect(font_destination_origin(2147483647, 0, 1).?).to_equal(2147483647)
expect(font_destination_origin(-2147483648, 0, 2).?).to_equal(-2147483648)
expect(font_destination_origin(2147483647, 0, 2)).to_be_nil()
expect(font_destination_origin(2147483647, 1, 1)).to_be_nil()
expect(font_destination_origin(-2147483648, -1, 1)).to_be_nil()
```

</details>

#### preserves device framebuffer truth when no font quad is submitted

- preserves device framebuffer truth when no font quad is submitted
   - Expected: backend.draw_font_batch(0, 0, invalid) equals `0`
   - Expected: backend.gpu_frame_complete is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves device framebuffer truth when no font quad is submitted")
var backend = MetalBackend.create()
backend.initialized = true
backend.gpu_frame_complete = true
backend.d_framebuffer = 1
val invalid = FontRenderBatch(program_version: 1, font_identity: "test-font", face_generation: 1, valid: false, atlas_width: 0, atlas_height: 0, atlas_pixels: [], quads: [], atlas_generation: 0, dirty_rects: [])
expect(backend.draw_font_batch(0, 0, invalid)).to_equal(0)
expect(backend.gpu_frame_complete).to_equal(true)
```

</details>

#### rejects unsupported font programs before Metal atlas mutation

- rejects unsupported font programs before Metal atlas mutation
   - Expected: backend.draw_font_batch(0, 0, batch) equals `0`
   - Expected: backend.font.atlas_generation equals `7`
   - Expected: backend.gpu_frame_complete is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unsupported font programs before Metal atlas mutation")
var backend = MetalBackend.create()
backend.initialized = true
backend.gpu_frame_complete = true
backend.d_framebuffer = 1
backend.font.atlas_generation = 7
for version in [0, -1, 2]:
    val batch = FontRenderBatch(program_version: version, font_identity: "test-font", face_generation: 1, valid: true, atlas_width: 1, atlas_height: 1,
        atlas_pixels: [1u32], quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0, width: 1, height: 1, atlas_x: 0, atlas_y: 0, color: 1u32)], atlas_generation: 8, dirty_rects: [])
    expect(backend.draw_font_batch(0, 0, batch)).to_equal(0)
    expect(backend.font.atlas_generation).to_equal(7)
    expect(backend.gpu_frame_complete).to_equal(true)
```

</details>

#### wires the typed Metal font backend only into native Metal constructors

- wires the typed Metal font backend only into native Metal constructors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wires the typed Metal font backend only into native Metal constructors")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
expect(source).to_contain("metal_backend: metal, w: width")
expect(source).to_contain("w: width, h: height, pacing: make_frame_pacing_counters(), selected_backend_name: \"metal-on-vulkan\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Metal font atlas companion.
- Metal font atlas companion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a58cad30519c66ad7ca66a32efa2afe7fc24cef5dcbdcb4938aab30d003a8d30`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a58cad30519c66ad7ca66a32efa2afe7fc24cef5dcbdcb4938aab30d003a8d30`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a58cad30519c66ad7ca66a32efa2afe7fc24cef5dcbdcb4938aab30d003a8d30`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'packs the frozen 13-word ABI into 52 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Metal's frozen 52-byte ABI behind overflow-safe source guards' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts atlas state invalidated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
