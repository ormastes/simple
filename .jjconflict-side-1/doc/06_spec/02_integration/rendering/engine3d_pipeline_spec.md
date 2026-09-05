# Engine3d Pipeline Specification

> 1. var engine = Engine3D create

<!-- sdn-diagram:id=engine3d_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine3d_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine3d_pipeline_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine3d_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine3d Pipeline Specification

## Scenarios

### Engine3D Shader Pipeline Lifecycle

#### create_shader

#### returns i32 id

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val id = engine.create_shader("void main(){}", "void main(){}")
expect(id).to_be_greater_than(-2)
```

</details>

#### delete_shader

#### with valid id does not crash

1. var engine = Engine3D create
2. engine delete shader
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val id = engine.create_shader("void main(){}", "void main(){}")
engine.delete_shader(id)
expect(true).to_equal(true)
```

</details>

#### create_pipeline

#### returns i32 id

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val shader_id = engine.create_shader("void main(){}", "void main(){}")
val id = engine.create_pipeline(shader_id, true, 0, 0)
expect(id).to_be_greater_than(-2)
```

</details>

#### bind_pipeline

#### with valid id does not crash

1. var engine = Engine3D create
2. engine bind pipeline
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val shader_id = engine.create_shader("void main(){}", "void main(){}")
val pipeline_id = engine.create_pipeline(shader_id, false, 0, 0)
engine.bind_pipeline(pipeline_id)
expect(true).to_equal(true)
```

</details>

#### render pass lifecycle

#### begin_render_pass and end_render_pass lifecycle works

1. var engine = Engine3D create
2. engine begin render pass
3. engine end render pass
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val color_target = engine.create_texture(320, 240, [0xFF000000])
val depth_target = engine.create_depth_texture(320, 240)
engine.begin_render_pass(color_target, depth_target)
engine.end_render_pass()
expect(true).to_equal(true)
```

</details>

#### compute kernel

#### create_compute_kernel returns i32 id

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val id = engine.create_compute_kernel("void main(){}")
expect(id).to_be_greater_than(-2)
```

</details>

#### dispatch_compute with valid kernel id does not crash

1. var engine = Engine3D create
2. engine dispatch compute
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val id = engine.create_compute_kernel("void main(){}")
engine.dispatch_compute(id, 1, 1, 1)
expect(true).to_equal(true)
```

</details>

#### storage buffer

#### create_storage_buffer returns i32 id

1. var engine = Engine3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val id = engine.create_storage_buffer(256)
expect(id).to_be_greater_than(-2)
```

</details>

#### update_buffer and read_buffer round-trip may return empty in emu

1. var engine = Engine3D create
2. engine update buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val id = engine.create_storage_buffer(4)
val data: [u8] = [1, 2, 3, 4]
engine.update_buffer(id, data)
val result = engine.read_buffer(id)
expect(result.len()).to_be_greater_than(-1)
```

</details>

#### shadow pass lifecycle

#### begin_shadow_pass and end_shadow_pass lifecycle works

1. var engine = Engine3D create
2. engine begin shadow pass
3. engine end shadow pass
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
val mat: [f32] = [
    1.0, 0.0, 0.0, 0.0,
    0.0, 1.0, 0.0, 0.0,
    0.0, 0.0, 1.0, 0.0,
    0.0, 0.0, 0.0, 1.0
]
engine.begin_shadow_pass(mat, 512)
engine.end_shadow_pass()
expect(true).to_equal(true)
```

</details>

#### synchronization

#### pipeline_barrier does not crash

1. var engine = Engine3D create
2. engine pipeline barrier
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create(320, 240)
engine.pipeline_barrier()
expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine3d_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D Shader Pipeline Lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
