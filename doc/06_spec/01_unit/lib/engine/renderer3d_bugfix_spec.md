# renderer3d_bugfix_spec

> Engine Renderer3D Bug Fix — ForwardRenderer3D regression tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# renderer3d_bugfix_spec

Engine Renderer3D Bug Fix — ForwardRenderer3D regression tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/renderer3d_bugfix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Renderer3D Bug Fix — ForwardRenderer3D regression tests

Tests that node positioning affects rendered output, verifies renderer
creation dimensions, and checks that empty scenes produce clear color only.

## Scenarios

### ForwardRenderer3D

#### creates with correct dimensions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates with correct dimensions
   - Expected: renderer.width equals `160`
   - Expected: renderer.height equals `120`
   - Expected: pixels.len() equals `19200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates with correct dimensions")
val renderer = ForwardRenderer3D.create(160, 120)
expect(renderer.width).to_equal(160)
expect(renderer.height).to_equal(120)
val pixels = renderer.get_pixels()
# Pixel buffer should be width * height
expect(pixels.len()).to_equal(19200)
```

</details>

#### render_scene with empty scene produces clear color only

- render_scene with empty scene produces clear color only
   - Expected: stats.draw_calls equals `0`
   - Expected: stats.triangles equals `0`
   - Expected: pixels.len() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("render_scene with empty scene produces clear color only")
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()
var renderer = ForwardRenderer3D.create(16, 16)
# Create camera only — no meshes
val cam_id = nodes.create_node("camera")
nodes.set_position(cam_id, Vec3(x: 0.0, y: 0.0, z: 5.0))
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
components.attach(cam_id, Component3D.Camera(data: cam))
# Clear and render empty scene
renderer.clear()
val stats = renderer.render_scene(nodes, components, cam_id)
# No draw calls because no meshes
expect(stats.draw_calls).to_equal(0)
expect(stats.triangles).to_equal(0)
# Pixels should still exist (all clear color)
val pixels = renderer.get_pixels()
expect(pixels.len()).to_equal(256)
```

</details>

#### render with positioned node produces different pixels than origin

- render with positioned node produces different pixels than origin
   - Expected: differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("render with positioned node produces different pixels than origin")
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()
var renderer_a = ForwardRenderer3D.create(32, 32)
var renderer_b = ForwardRenderer3D.create(32, 32)
# Camera
val cam_id = nodes.create_node("camera")
nodes.set_position(cam_id, Vec3(x: 0.0, y: 0.0, z: 10.0))
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
components.attach(cam_id, Component3D.Camera(data: cam))
# Light
val light_id = nodes.create_node("light")
val light = directional_light(Vec3(x: 0.0, y: -1.0, z: -1.0), EngineColor.white(), 1.0)
components.attach(light_id, Component3D.Light(data: light))
# Mesh at origin
val mesh_id = nodes.create_node("cube_origin")
val mesh = create_cube(1.0)
val material = unlit_material(EngineColor.red())
components.attach(mesh_id, Component3D.Mesh(mesh: mesh, material: material))
# Render A: mesh at origin
renderer_a.clear()
val stats_a = renderer_a.render_scene(nodes, components, cam_id)
val pixels_a = renderer_a.get_pixels()
# Move mesh off to the side
nodes.set_position(mesh_id, Vec3(x: 5.0, y: 0.0, z: 0.0))
# Render B: mesh displaced
renderer_b.clear()
val stats_b = renderer_b.render_scene(nodes, components, cam_id)
val pixels_b = renderer_b.get_pixels()
# Both should have drawn something
expect(stats_a.draw_calls).to_be_greater_than(0)
expect(stats_b.draw_calls).to_be_greater_than(0)
# Pixels should differ (different positions produce different images)
var differ = false
var i = 0
while i < pixels_a.len():
    if pixels_a[i] != pixels_b[i]:
        differ = true
    i = i + 1
expect(differ).to_equal(true)
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `651856f7f598cc77553f5b4d5a997147ce831d5f0fdb4016b30ee52c1f4ef76a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `651856f7f598cc77553f5b4d5a997147ce831d5f0fdb4016b30ee52c1f4ef76a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `651856f7f598cc77553f5b4d5a997147ce831d5f0fdb4016b30ee52c1f4ef76a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/engine/renderer3d_bugfix_spec.spl
mirror: doc/06_spec/01_unit/lib/engine/renderer3d_bugfix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/engine/renderer3d_bugfix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/engine/renderer3d_bugfix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/engine/renderer3d_bugfix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/engine/renderer3d_bugfix_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with correct dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/renderer3d_bugfix_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'render_scene with empty scene produces clear color only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/renderer3d_bugfix_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'render with positioned node produces different pixels than origin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
