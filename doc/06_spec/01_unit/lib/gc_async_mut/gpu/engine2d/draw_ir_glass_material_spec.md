# draw_ir_glass_material_spec

> Engine2D canonical CPU-composited glass material pixel specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# draw_ir_glass_material_spec

Engine2D canonical CPU-composited glass material pixel specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine2D canonical CPU-composited glass material pixel specification.

## Scenarios

### Engine2D Draw IR glass material pixels

#### preserves rounded corners and alpha-composites the surface

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves rounded corners and alpha-composites the surface
   - Expected: pixels.len() equals `16`
   - Expected: pixels[0] equals `black`
   - Expected: pixels[5] equals `0xFF7F7F7Fu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves rounded corners and alpha-composites the surface")
val black: u32 = 0xFF000000u32
val white: u32 = 0xFFFFFFFFu32
val framebuffer: [u32] = [black; 64]
val pixels = engine2d_draw_ir_glass_material_pixels(
    framebuffer,
    Engine2dGlassMaterialConfig(
        framebuffer_width: 8,
        framebuffer_height: 8,
        x: 2,
        y: 2,
        width: 4,
        height: 4,
        radius: 1,
        blur_radius: 0,
        saturation_milli: 1000,
        surface_alpha_milli: 500,
        surface_color: white,
        gradient_from: white,
        gradient_to: white,
        gradient_enabled: false,
        gradient_layered_over_surface: false
    )
)

expect(pixels.len()).to_equal(16)
expect(pixels[0]).to_equal(black)
expect(pixels[5]).to_equal(0xFF7F7F7Fu32)
```

</details>

#### samples the existing framebuffer with bounded box blur

- samples the existing framebuffer with bounded box blur
   - Expected: pixels equals `[0xFFE2E2E2u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("samples the existing framebuffer with bounded box blur")
val white: u32 = 0xFFFFFFFFu32
var framebuffer: [u32] = [white; 25]
framebuffer[12] = 0xFF000000u32
val pixels = engine2d_draw_ir_glass_material_pixels(
    framebuffer,
    Engine2dGlassMaterialConfig(
        framebuffer_width: 5,
        framebuffer_height: 5,
        x: 2,
        y: 2,
        width: 1,
        height: 1,
        radius: 0,
        blur_radius: 1,
        saturation_milli: 1000,
        surface_alpha_milli: 0,
        surface_color: 0u32,
        gradient_from: 0u32,
        gradient_to: 0u32,
        gradient_enabled: false,
        gradient_layered_over_surface: false
    )
)

expect(pixels).to_equal([0xFFE2E2E2u32])
```

</details>

#### clips and alpha-composites both gradient endpoints

- clips and alpha-composites both gradient endpoints
   - Expected: pixels equals `[0xFF7F0000u32, 0xFF007F00u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clips and alpha-composites both gradient endpoints")
val black: u32 = 0xFF000000u32
val framebuffer: [u32] = [black; 4]
val pixels = engine2d_draw_ir_glass_material_pixels(
    framebuffer,
    Engine2dGlassMaterialConfig(
        framebuffer_width: 2,
        framebuffer_height: 2,
        x: 0,
        y: 0,
        width: 1,
        height: 2,
        radius: 0,
        blur_radius: 0,
        saturation_milli: 1000,
        surface_alpha_milli: 500,
        surface_color: 0u32,
        gradient_from: 0xFFFF0000u32,
        gradient_to: 0xFF00FF00u32,
        gradient_enabled: true,
        gradient_layered_over_surface: false
    )
)

expect(pixels).to_equal([0xFF7F0000u32, 0xFF007F00u32])
```

</details>

#### applies backdrop saturation before the surface tint

- applies backdrop saturation before the surface tint
   - Expected: pixels equals `[0xFF363636u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("applies backdrop saturation before the surface tint")
val framebuffer: [u32] = [0xFFFF0000u32]
val pixels = engine2d_draw_ir_glass_material_pixels(
    framebuffer,
    Engine2dGlassMaterialConfig(
        framebuffer_width: 1,
        framebuffer_height: 1,
        x: 0,
        y: 0,
        width: 1,
        height: 1,
        radius: 0,
        blur_radius: 0,
        saturation_milli: 0,
        surface_alpha_milli: 0,
        surface_color: 0u32,
        gradient_from: 0u32,
        gradient_to: 0u32,
        gradient_enabled: false,
        gradient_layered_over_surface: false
    )
)

expect(pixels).to_equal([0xFF363636u32])
```

</details>

#### rejects oversized blur work before allocating an intermediate buffer

- rejects oversized blur work before allocating an intermediate buffer
   - Expected: pixels equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects oversized blur work before allocating an intermediate buffer")
val pixels = engine2d_draw_ir_glass_material_pixels(
    [],
    Engine2dGlassMaterialConfig(
        framebuffer_width: 8388608,
        framebuffer_height: 1,
        x: 0,
        y: 0,
        width: 8388608,
        height: 1,
        radius: 0,
        blur_radius: 4,
        saturation_milli: 1000,
        surface_alpha_milli: 0,
        surface_color: 0u32,
        gradient_from: 0u32,
        gradient_to: 0u32,
        gradient_enabled: false,
        gradient_layered_over_surface: false
    )
)

expect(pixels).to_equal([])
```

</details>

#### composites an alpha gradient over the translucent base surface

- composites an alpha gradient over the translucent base surface
   - Expected: pixels equals `[0xFF3F0080u32]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites an alpha gradient over the translucent base surface")
val pixels = engine2d_draw_ir_glass_material_pixels(
    [0xFF000000u32],
    Engine2dGlassMaterialConfig(
        framebuffer_width: 1,
        framebuffer_height: 1,
        x: 0,
        y: 0,
        width: 1,
        height: 1,
        radius: 0,
        blur_radius: 0,
        saturation_milli: 1000,
        surface_alpha_milli: 500,
        surface_color: 0xFFFF0000u32,
        gradient_from: 0x800000FFu32,
        gradient_to: 0x800000FFu32,
        gradient_enabled: true,
        gradient_layered_over_surface: true
    )
)

expect(pixels).to_equal([0xFF3F0080u32])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `0cff64fa8b9af117997eb0777733c6a18dcbc00ef5ee473d487c5632a18d8650`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0cff64fa8b9af117997eb0777733c6a18dcbc00ef5ee473d487c5632a18d8650`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0cff64fa8b9af117997eb0777733c6a18dcbc00ef5ee473d487c5632a18d8650`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves rounded corners and alpha-composites the surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'samples the existing framebuffer with bounded box blur' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clips and alpha-composites both gradient endpoints' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
