# Gpu Lighting3d Specification

> <details>

<!-- sdn-diagram:id=gpu_lighting3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_lighting3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_lighting3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_lighting3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Lighting3d Specification

## Scenarios

### Stream D: LightUniform construction

### directional light

#### AC-4: light_type is 0 for directional

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_directional_light()
expect(light.light_type).to_equal(0)
```

</details>

#### AC-4: intensity is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_directional_light()
expect(light.intensity).to_equal(1.0)
```

</details>

#### AC-4: position_y is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_directional_light()
expect(light.position_y).to_equal(10.0)
```

</details>

#### AC-4: color_r is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_directional_light()
expect(light.color_r).to_equal(1.0)
```

</details>

### point light

#### AC-4: light_type is 1 for point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_point_light()
expect(light.light_type).to_equal(1)
```

</details>

#### AC-4: position_x is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_point_light()
expect(light.position_x).to_equal(5.0)
```

</details>

#### AC-4: intensity is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_point_light()
expect(light.intensity).to_equal(2.0)
```

</details>

### spot light

#### AC-4: light_type is 2 for spot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val light = make_spot_light()
expect(light.light_type).to_equal(2)
```

</details>

### Stream D: GpuLightingState init

### gpu_lighting_init

#### AC-4: light_buf id is valid after init

1. var backend = make software backend inited


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 8)
expect(state.light_buf.id).to_be_greater_than(-1)
```

</details>

#### AC-4: max_lights matches requested count

1. var backend = make software backend inited
   - Expected: state.max_lights equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 8)
expect(state.max_lights).to_equal(8)
```

</details>

#### AC-4: light_count starts at 0

1. var backend = make software backend inited
   - Expected: state.light_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 8)
expect(state.light_count).to_equal(0)
```

</details>

#### AC-4: max_lights of 1 is valid

1. var backend = make software backend inited
   - Expected: state.max_lights equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 1)
expect(state.max_lights).to_equal(1)
```

</details>

### Stream D: gpu_lighting_upload

### upload single light

#### AC-4: upload does not crash with one directional light

1. var backend = make software backend inited
   - Expected: uploaded.light_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 4)
val lights = [make_directional_light()]
val uploaded = gpu_lighting_upload(state, backend, lights)
expect(uploaded.light_count).to_equal(1)
```

</details>

#### AC-4: upload does not crash with one point light

1. var backend = make software backend inited
   - Expected: uploaded.light_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 4)
val lights = [make_point_light()]
val uploaded = gpu_lighting_upload(state, backend, lights)
expect(uploaded.light_count).to_equal(1)
```

</details>

### upload multiple lights

#### AC-4: upload does not crash with two lights

1. var backend = make software backend inited
   - Expected: uploaded.light_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 4)
val lights = [make_directional_light(), make_point_light()]
val uploaded = gpu_lighting_upload(state, backend, lights)
expect(uploaded.light_count).to_equal(2)
```

</details>

#### AC-4: upload does not crash with three lights

1. var backend = make software backend inited
   - Expected: uploaded.light_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 4)
val lights = [make_directional_light(), make_point_light(), make_spot_light()]
val uploaded = gpu_lighting_upload(state, backend, lights)
expect(uploaded.light_count).to_equal(3)
```

</details>

### Stream D: gpu_lighting_bind

### bind to render pass

#### AC-4: bind does not crash with initialized state

1. var backend = make software backend inited
2. backend begin frame
3. gpu lighting bind
   - Expected: backend.active_pass.pass_id equals `rph.id`
4. backend end render pass
5. backend end frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 4)
val lights = [make_directional_light()]
val uploaded = gpu_lighting_upload(state, backend, lights)
backend.begin_frame()
val rph = make_render_pass(backend)
gpu_lighting_bind(uploaded, backend, rph)
expect(backend.active_pass.pass_id).to_equal(rph.id)
backend.end_render_pass(rph)
backend.end_frame()
```

</details>

#### AC-4: bind with empty light list does not crash

1. var backend = make software backend inited
2. backend begin frame
3. gpu lighting bind
4. backend end render pass
5. backend end frame
   - Expected: backend.active_pass.pass_id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val state = gpu_lighting_init(backend, 4)
val empty_lights = [] as [LightUniform]
val uploaded = gpu_lighting_upload(state, backend, empty_lights)
backend.begin_frame()
val rph = make_render_pass(backend)
gpu_lighting_bind(uploaded, backend, rph)
backend.end_render_pass(rph)
backend.end_frame()
expect(backend.active_pass.pass_id).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stream D: LightUniform construction
- directional light
- point light
- spot light
- Stream D: GpuLightingState init
- gpu_lighting_init
- Stream D: gpu_lighting_upload
- upload single light
- upload multiple lights
- Stream D: gpu_lighting_bind
- bind to render pass

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
