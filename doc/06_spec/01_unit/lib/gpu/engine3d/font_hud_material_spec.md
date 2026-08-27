# Font Hud Material Specification

> Tests covering Engine3D Vulkan font atlas identity, Engine3D Metal font HUD material.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Hud Material Specification

## Scenarios

### Engine3D Vulkan font atlas identity

#### fences the atlas cache with Vulkan graphics target and session identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fences the atlas cache with Vulkan graphics target and session identity
   - Expected: source.index_of("if (self.font_artifact_sha256 == \"\"") < source.index_of("sha256_u8_hex(font_hud_vulkan_vertex_spirv())") is true
   - Expected: source.split("sha256_u8_hex(font_hud_vulkan_vertex_spirv())").len() equals `2`
   - Expected: source.split("sha256_u8_hex(font_world_vulkan_vertex_spirv())").len() equals `2`
   - Expected: source.split("sha256_u8_hex(font_vulkan_fragment_spirv())").len() equals `2`
   - Expected: eager_handle_form_present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
# @req REQ-SSPEC-UNIT
step("fences the atlas cache with Vulkan graphics target and session identity")
val source = file_read("src/lib/gc_async_mut/gpu/engine3d/vulkan_font_adapter.spl")
expect source to_contain "font_atlas_composite_cache_identity("
expect source to_contain "font_render_batch_atlas_owner_identity(batch), \"vulkan3d\", device_features"
expect source to_contain "if (self.font_artifact_sha256 == \"\""
expect(source.index_of("if (self.font_artifact_sha256 == \"\"") < source.index_of("sha256_u8_hex(font_hud_vulkan_vertex_spirv())")).to_equal(true)
expect(source.split("sha256_u8_hex(font_hud_vulkan_vertex_spirv())").len()).to_equal(2)  # oracle: exactly one fence definition plus one use
expect(source.split("sha256_u8_hex(font_world_vulkan_vertex_spirv())").len()).to_equal(2)  # oracle: exactly one fence definition plus one use
expect(source.split("sha256_u8_hex(font_vulkan_fragment_spirv())").len()).to_equal(2)  # oracle: exactly one fence definition plus one use
expect source to_contain "sha256_u8_hex(font_hud_vulkan_vertex_spirv())"
expect source to_contain "sha256_u8_hex(font_world_vulkan_vertex_spirv())"
expect source to_contain "sha256_u8_hex(font_vulkan_fragment_spirv())"
expect source to_contain "self.font_artifact_sha256 + \";hud=\""
expect source to_contain "artifact_identity, dependency_identity"
expect source to_contain "self.font_artifact_sha256 = \"\""
# the eager pipeline-handle form must NOT have replaced the lazy sha256 fence
val eager_handle_form_present = source.contains("val artifact_identity = if self.backend.pipeline_native_handle(self.hud_pipeline) > 0 and self.backend.pipeline_native_handle(self.world_pipeline) > 0:\n            \"hud=\"")
expect(eager_handle_form_present).to_equal(false)
```

</details>

#### pins the fragment shader that discards zero-coverage depth fragments

- pins the fragment shader that discards zero-coverage depth fragments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins the fragment shader that discards zero-coverage depth fragments")
val fragment = font_vulkan_fragment_spirv()
expect fragment.len() to_equal 1180
expect sha256_u8_hex(fragment) to_equal "f4d2dd66dc65502c94a9c90bae1cb4681fa3b55d2fd8ea34605960fde9312ab4"
```

</details>

#### reuploads when any target identity component or generation changes

- reuploads when any target identity component or generation changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuploads when any target identity component or generation changes")
val batch = FontRenderBatch(program_version: 1, font_identity: "face-a", face_generation: 3,
    valid: true, atlas_width: 2, atlas_height: 4,
    atlas_pixels: [0u32; 8], quads: [], atlas_generation: 7, dirty_rects: [])
val material = batch.atlas_owner_identity()
val owner = font_atlas_composite_cache_identity(material, "vulkan3d", "device", "artifact", "dependency")
val other = FontRenderBatch(program_version: 1, font_identity: "face-b", face_generation: 3,
    valid: true, atlas_width: 2, atlas_height: 4,
    atlas_pixels: [0u32; 8], quads: [], atlas_generation: 7, dirty_rects: [])
expect vulkan_font_atlas_upload_required(owner, 7, owner, batch) to_equal false
expect vulkan_font_atlas_upload_required(owner, 6, owner, batch) to_equal true
expect vulkan_font_atlas_upload_required(owner, 7, font_atlas_composite_cache_identity(other.atlas_owner_identity(), "vulkan3d", "device", "artifact", "dependency"), batch) to_equal true
expect vulkan_font_atlas_upload_required(owner, 7, font_atlas_composite_cache_identity(material, "vulkan3d", "device-2", "artifact", "dependency"), batch) to_equal true
expect vulkan_font_atlas_upload_required(owner, 7, font_atlas_composite_cache_identity(material, "vulkan3d", "device", "artifact-2", "dependency"), batch) to_equal true
expect vulkan_font_atlas_upload_required(owner, 7, font_atlas_composite_cache_identity(material, "vulkan3d", "device", "artifact", "dependency-2"), batch) to_equal true
expect vulkan_font_atlas_upload_required("", -1, "", batch) to_equal true
```

</details>

### Engine3D Metal font HUD material

#### shares one canonical vertex stream across native backends

- shares one canonical vertex stream across native backends


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shares one canonical vertex stream across native backends")
val quad = FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
    width: 2, height: 1, atlas_x: 1, atlas_y: 0, color: 0x80402010u32)
expect font_hud_vertices(_hud_batch(quad), 0, 0, 4, 2) to_equal font_hud_metal_vertices(_hud_batch(quad), 0, 0, 4, 2)
```

</details>

#### expands one validated quad to six little-endian 20-byte vertices

- expands one validated quad to six little-endian 20-byte vertices


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("expands one validated quad to six little-endian 20-byte vertices")
val quad = FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
    width: 2, height: 1, atlas_x: 1, atlas_y: 0, color: 0x80402010u32)
val bytes = font_hud_metal_vertices(_hud_batch(quad), 0, 0, 4, 2)
expect bytes.len() to_equal 120
expect _u32_le(bytes, 0) to_equal f32_to_bits(-1.0f32)
expect _u32_le(bytes, 4) to_equal f32_to_bits(1.0f32)
expect _u32_le(bytes, 8) to_equal f32_to_bits(0.25f32)
expect _u32_le(bytes, 12) to_equal f32_to_bits(0.0f32)
expect _u32_le(bytes, 16) to_equal 0x80402010u32
expect _u32_le(bytes, 100) to_equal f32_to_bits(0.0f32)
expect _u32_le(bytes, 104) to_equal f32_to_bits(0.0f32)
expect _u32_le(bytes, 108) to_equal f32_to_bits(0.75f32)
expect _u32_le(bytes, 112) to_equal f32_to_bits(0.5f32)
```

</details>

#### carries clip depth in the separate 24-byte world vertex contract

- carries clip depth in the separate 24-byte world vertex contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries clip depth in the separate 24-byte world vertex contract")
val quad = FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
    width: 2, height: 1, atlas_x: 1, atlas_y: 0, color: 0x80402010u32)
val bytes = font_world_vertices(_hud_batch(quad), 0, 0, 4, 2, 0.25f32)
expect bytes.len() to_equal 144
expect _u32_le(bytes, 8) to_equal f32_to_bits(0.625f32)
expect _u32_le(bytes, 12) to_equal f32_to_bits(0.25f32)
expect _u32_le(bytes, 20) to_equal 0x80402010u32
```

</details>

#### maps OpenGL clip depth to Vulkan device depth

- maps OpenGL clip depth to Vulkan device depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps OpenGL clip depth to Vulkan device depth")
expect font_world_vulkan_depth(-1.0f32) to_equal 0.0f32
expect font_world_vulkan_depth(0.0f32) to_equal 0.5f32
expect font_world_vulkan_depth(1.0f32) to_equal 1.0f32
val quad = FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
    width: 2, height: 1, atlas_x: 1, atlas_y: 0, color: 0x80402010u32)
expect _u32_le(font_world_vertices(_hud_batch(quad), 0, 0, 4, 2, -1.0f32), 8) to_equal f32_to_bits(0.0f32)
expect _u32_le(font_world_vertices(_hud_batch(quad), 0, 0, 4, 2, 1.0f32), 8) to_equal f32_to_bits(1.0f32)
```

</details>

#### fails closed before emitting a partial vertex stream

- fails closed before emitting a partial vertex stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed before emitting a partial vertex stream")
val bad_atlas = FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
    width: 2, height: 1, atlas_x: 3, atlas_y: 0, color: 0xFFFFFFFFu32)
expect font_hud_metal_vertices(_hud_batch(bad_atlas), 0, 0, 4, 2).len() to_equal 0
val bad_destination = FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 2147483647, dst_y: 0,
    width: 2, height: 1, atlas_x: 0, atlas_y: 0, color: 0xFFFFFFFFu32)
expect font_hud_metal_vertices(_hud_batch(bad_destination), 1, 0, 4, 2).len() to_equal 0
val invalid = FontRenderBatch(program_version: 1, font_identity: "test-font", face_generation: 1, valid: false, atlas_width: 4, atlas_height: 2,
    atlas_pixels: [0u32; 8], quads: [bad_atlas], atlas_generation: 1, dirty_rects: [])
expect font_hud_metal_vertices(invalid, 0, 0, 4, 2).len() to_equal 0
```

</details>

#### rejects invalid depth, atlas storage, and vertex-size overflow

- rejects invalid depth, atlas storage, and vertex-size overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid depth, atlas storage, and vertex-size overflow")
val quad = FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0,
    width: 2, height: 1, atlas_x: 1, atlas_y: 0, color: 0xFFFFFFFFu32)
expect font_world_vertices(_hud_batch(quad), 0, 0, 4, 2, -1.01f32).len() to_equal 0
expect font_world_vertices(_hud_batch(quad), 0, 0, 4, 2, 1.01f32).len() to_equal 0
val short_atlas = FontRenderBatch(program_version: 1, font_identity: "test-font", face_generation: 1,
    valid: true, atlas_width: 4, atlas_height: 2, atlas_pixels: [0u32; 7],
    quads: [quad], atlas_generation: 1, dirty_rects: [])
expect font_hud_vertices(short_atlas, 0, 0, 4, 2).len() to_equal 0
expect font_vertex_bytes_checked(1, 24) to_equal 144
expect font_vertex_bytes_checked(14913081, 24) to_equal -1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine3D Vulkan font atlas identity, Engine3D Metal font HUD material.
- Engine3D Vulkan font atlas identity
- Engine3D Metal font HUD material

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `9dfd96faba1059627983254d9e11b1aade82e8acc4ac8898155ae37189105647`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dfd96faba1059627983254d9e11b1aade82e8acc4ac8898155ae37189105647`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dfd96faba1059627983254d9e11b1aade82e8acc4ac8898155ae37189105647`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine3d/font_hud_material_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine3d/font_hud_material_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine3d/font_hud_material_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fences the atlas cache with Vulkan graphics target and session identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pins the fragment shader that discards zero-coverage depth fragments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine3d/font_hud_material_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuploads when any target identity component or generation changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
