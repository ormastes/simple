# Wm Scene Metal Offload Specification

> <details>

<!-- sdn-diagram:id=wm_scene_metal_offload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_scene_metal_offload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_scene_metal_offload_spec -> std
wm_scene_metal_offload_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_scene_metal_offload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Scene Metal Offload Specification

## Scenarios

### GUI WM scene Metal GPU offload

#### projects the WM scene into a non-empty Draw IR composition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val comp = _composition()
# desktop + chrome + one window batch
expect(comp.batches.len()).to_be_greater_than(2)
expect(comp.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

#### renders the WM composition on the CPU backend (oracle baseline)

- var cpu = Engine2D create with backend
   - Expected: cpu.backend_name() equals `cpu`
   - Expected: _nonzero(cpu.read_pixels()) equals `SCENE_W * SCENE_H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cpu = Engine2D.create_with_backend(SCENE_W, SCENE_H, "cpu")
val result = engine2d_draw_ir_adv_composition(cpu, _composition(), false)
expect(cpu.backend_name()).to_equal("cpu")
expect(result.rendered_command_count).to_be_greater_than(0)
# the desktop fill covers the whole framebuffer
expect(_nonzero(cpu.read_pixels())).to_equal(SCENE_W * SCENE_H)
```

</details>

#### Metal strict availability

#### reports Metal availability consistently with the platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Engine2D.create_with_backend_strict(16, 16, "metal")
if is_macos():
    expect(result.is_ok()).to_equal(true)
else:
    expect(result.is_ok()).to_equal(false)
```

</details>

#### on macOS: WM scene renders bit-exact on Metal GPU

#### selects the Metal backend and matches the CPU oracle pixel-for-pixel

- var cpu = Engine2D create with backend
- var metal = Engine2D create with backend
   - Expected: metal.backend_name() equals `metal`
   - Expected: metal_result.rendered_command_count equals `cpu_result.rendered_command_count`
   - Expected: _diffcount(cpu_px, metal_px) equals `0`
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    val comp = _composition()

    var cpu = Engine2D.create_with_backend(SCENE_W, SCENE_H, "cpu")
    val cpu_result = engine2d_draw_ir_adv_composition(cpu, comp, false)
    val cpu_px = cpu.read_pixels()

    var metal = Engine2D.create_with_backend(SCENE_W, SCENE_H, "metal")
    val metal_result = engine2d_draw_ir_adv_composition(metal, comp, true)
    val metal_px = metal.read_pixels()

    expect(metal.backend_name()).to_equal("metal")
    expect(metal_result.rendered_command_count).to_equal(cpu_result.rendered_command_count)
    expect(_nonzero(metal_px)).to_be_greater_than(0)
    # GPU offload must be bit-exact with the CPU reference render
    expect(_diffcount(cpu_px, metal_px)).to_equal(0)
else:
    # Non-macOS hosts have no Metal device; covered by the strict test.
    expect(is_macos()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/wm_scene_metal_offload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GUI WM scene Metal GPU offload

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
