# Engine Component Facade Specification

> Tests covering nogc_async_mut engine component facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Component Facade Specification

## Scenarios

### nogc_async_mut engine component facade

#### re-exports 2D registry and helper extensions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports 2D registry and helper extensions
   - Expected: reg.get_components(node).len() equals `0`
   - Expected: sprite_component.is_sprite() is true
   - Expected: sprite_component.type_name() equals `Sprite`
   - Expected: screen.x equals `400.0`
   - Expected: tilemap.get_tile(TileCoord(col: 1, row: 1)).value equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports 2D registry and helper extensions")
val node = NodeId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val tex = TextureId(raw: RawHandle(index: 2, generation: Generation(value: 1)))
val sprite = SpriteData(
    texture_id: tex,
    src_rect: Rect2(x: 0.0, y: 0.0, width: 16.0, height: 16.0),
    pivot: Vec2(x: 0.5, y: 0.5),
    flip_x: false,
    flip_y: false,
    tint: EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
)
val reg = ComponentRegistry.create()
expect(reg.get_components(node).len()).to_equal(0)
val sprite_component = Component2D.Sprite(data: sprite)
expect(sprite_component.is_sprite()).to_equal(true)
expect(sprite_component.type_name()).to_equal("Sprite")

val cam = CameraData.create(800.0, 600.0)
val screen = cam.world_to_screen(Vec2(x: 0.0, y: 0.0), Vec2.zero())
expect(screen.x).to_equal(400.0)

val tilemap = TileMapData.create(tex, 16, 16, 4, 4).set_tile(TileCoord(col: 1, row: 1), TileIndex(value: 7))
expect(tilemap.get_tile(TileCoord(col: 1, row: 1)).value).to_equal(7)
```

</details>

#### re-exports mesh and 3D registry surfaces

- re-exports mesh and 3D registry surfaces
   - Expected: cube.vertex_count() equals `24`
   - Expected: reg3d.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports mesh and 3D registry surfaces")
val cube = create_cube(2.0)
expect(cube.vertex_count()).to_equal(24)
val reg3d = ComponentRegistry3D.create()
expect(reg3d.entries.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut engine component facade.
- nogc_async_mut engine component facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `2f4fcc10526a9e38a150820db0f8da49a975b88d14b3517ff1d3ef5185b04a0f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f4fcc10526a9e38a150820db0f8da49a975b88d14b3517ff1d3ef5185b04a0f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f4fcc10526a9e38a150820db0f8da49a975b88d14b3517ff1d3ef5185b04a0f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports 2D registry and helper extensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/engine/component/engine_component_facade_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports mesh and 3D registry surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
