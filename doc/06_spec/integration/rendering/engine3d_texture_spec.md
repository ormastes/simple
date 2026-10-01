# engine3d_texture_spec

> Purpose: This spec proves Engine3D Texture Operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine3d_texture_spec

Purpose: This spec proves Engine3D Texture Operations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine3d_texture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Engine3D Texture Operations.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Engine3D Texture Operations

#### engine construction

#### Engine3D.create creates engine with 320x240

- Engine3D.create creates engine with 320x240
   - Expected: engine._w equals `320`
   - Expected: engine._h equals `240`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-ENGINE3DTEXTURE-001
step("Engine3D.create creates engine with 320x240")
var engine = Engine3D.create(320, 240)
expect(engine._w).to_equal(320)
expect(engine._h).to_equal(240)
```

</details>

#### load_texture

#### returns handle with correct width and height

- returns handle with correct width and height
- returns handle with correct width and height
   - Expected: handle.width equals `64`
   - Expected: handle.height equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns handle with correct width and height")
step("returns handle with correct width and height")
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
val handle = engine.load_texture(64, 64, pixels)
expect(handle.width).to_equal(64)
expect(handle.height).to_equal(64)
```

</details>

#### returns handle with gpu_id >= -1 in emu

- returns handle with gpu_id >= -1 in emu
- returns handle with gpu_id >= -1 in emu


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns handle with gpu_id >= -1 in emu")
step("returns handle with gpu_id >= -1 in emu")
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
val handle = engine.load_texture(64, 64, pixels)
expect(handle.gpu_id).to_be_greater_than(-2)
```

</details>

#### load_depth_texture

#### returns handle with format TEX_FMT_DEPTH32_FLOAT

- returns handle with format TEX_FMT_DEPTH32_FLOAT
- returns handle with format TEX_FMT_DEPTH32_FLOAT
   - Expected: handle.format equals `TEX_FMT_DEPTH32_FLOAT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns handle with format TEX_FMT_DEPTH32_FLOAT")
step("returns handle with format TEX_FMT_DEPTH32_FLOAT")
var engine = Engine3D.create(320, 240)
val handle = engine.load_depth_texture(128, 128)
expect(handle.format).to_equal(TEX_FMT_DEPTH32_FLOAT)
```

</details>

#### load_cubemap

#### returns handle with depth 6

- returns handle with depth 6
- returns handle with depth 6
   - Expected: handle.depth equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns handle with depth 6")
step("returns handle with depth 6")
var engine = Engine3D.create(320, 240)
val face: [u32] = [0xFF000000]
val faces: [[u32]] = [face, face, face, face, face, face]
val handle = engine.load_cubemap(64, faces)
expect(handle.depth).to_equal(6)
```

</details>

#### unload_texture

#### after unload resource_pool texture_count decrements

- after unload resource_pool texture_count decrements
- after unload resource_pool texture_count decrements
   - Expected: after equals `before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("after unload resource_pool texture_count decrements")
step("after unload resource_pool texture_count decrements")
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
val handle = engine.load_texture(64, 64, pixels)
val before = engine.resource_pool().texture_count()
engine.unload_texture(handle)
val after = engine.resource_pool().texture_count()
expect(after).to_equal(before - 1)
```

</details>

#### load_shader and unload_shader

#### load_shader returns handle with valid id

- load_shader returns handle with valid id
- load_shader returns handle with valid id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("load_shader returns handle with valid id")
step("load_shader returns handle with valid id")
var engine = Engine3D.create(320, 240)
val handle = engine.load_shader("void main(){}", "void main(){}")
expect(handle.id).to_be_greater_than(0)
```

</details>

#### unload_shader frees the shader

- unload_shader frees the shader
- unload_shader frees the shader
   - Expected: after equals `before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unload_shader frees the shader")
step("unload_shader frees the shader")
var engine = Engine3D.create(320, 240)
val handle = engine.load_shader("void main(){}", "void main(){}")
val before = engine.resource_pool().shader_count()
engine.unload_shader(handle)
val after = engine.resource_pool().shader_count()
expect(after).to_equal(before - 1)
```

</details>

#### load_buffer and unload_buffer

#### load_buffer returns handle with valid id

- load_buffer returns handle with valid id
- load_buffer returns handle with valid id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("load_buffer returns handle with valid id")
step("load_buffer returns handle with valid id")
var engine = Engine3D.create(320, 240)
val handle = engine.load_buffer(1024)
expect(handle.id).to_be_greater_than(0)
```

</details>

#### unload_buffer frees the buffer

- unload_buffer frees the buffer
- unload_buffer frees the buffer
   - Expected: after equals `before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unload_buffer frees the buffer")
step("unload_buffer frees the buffer")
var engine = Engine3D.create(320, 240)
val handle = engine.load_buffer(1024)
val before = engine.resource_pool().buffer_count()
engine.unload_buffer(handle)
val after = engine.resource_pool().buffer_count()
expect(after).to_equal(before - 1)
```

</details>

#### load_pipeline

#### creates pipeline from shader handle

- creates pipeline from shader handle
- creates pipeline from shader handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates pipeline from shader handle")
step("creates pipeline from shader handle")
var engine = Engine3D.create(320, 240)
val shader = engine.load_shader("void main(){}", "void main(){}")
val pipeline = engine.load_pipeline(shader, true, 0, 0)
expect(pipeline.id).to_be_greater_than(0)
```

</details>

#### gc_resources

#### after loading and not touching gc removes stale resources

- after loading and not touching gc removes stale resources
- after loading and not touching gc removes stale resources
   - Expected: engine.resource_pool().texture_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("after loading and not touching gc removes stale resources")
step("after loading and not touching gc removes stale resources")
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
engine.load_texture(32, 32, pixels)
engine.resource_pool().advance_frame()
engine.resource_pool().advance_frame()
engine.gc_resources(1)
expect(engine.resource_pool().texture_count()).to_equal(1)
```

</details>

#### resource_pool total_resource_count

#### matches expected count after operations

- matches expected count after operations
- matches expected count after operations
   - Expected: engine.resource_pool().total_resource_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches expected count after operations")
step("matches expected count after operations")
var engine = Engine3D.create(320, 240)
val pixels: [u32] = [0xFFFFFFFF]
engine.load_texture(32, 32, pixels)
val shader = engine.load_shader("void main(){}", "void main(){}")
engine.load_buffer(256)
expect(engine.resource_pool().total_resource_count()).to_equal(3)
```

</details>

#### create_texture_ex

#### with TextureDescriptor3D.create_2d returns i32

- with TextureDescriptor3D.create_2d returns i32
- with TextureDescriptor3D.create_2d returns i32


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("with TextureDescriptor3D.create_2d returns i32")
step("with TextureDescriptor3D.create_2d returns i32")
var engine = Engine3D.create(320, 240)
val desc = TextureDescriptor3D.create_2d(64, 64, TEX_FMT_RGBA8_UNORM)
val data: [u8] = []
val id = engine.create_texture_ex(desc, data)
expect(id).to_be_greater_than(-2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-ENGINE3DTEXTURE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb857512634bc8e948405738e274e1f8651918256e53718978d84ac7877fbbdd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb857512634bc8e948405738e274e1f8651918256e53718978d84ac7877fbbdd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb857512634bc8e948405738e274e1f8651918256e53718978d84ac7877fbbdd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/engine3d_texture_spec.spl
mirror: doc/06_spec/integration/rendering/engine3d_texture_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine3d_texture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine3d_texture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine3d_texture_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine3d_texture_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Engine3D.create creates engine with 320x240' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine3d_texture_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns handle with correct width and height' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine3d_texture_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns handle with gpu_id >= -1 in emu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
