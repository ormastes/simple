# Gpu Mesh3d Specification

> <details>

<!-- sdn-diagram:id=gpu_mesh3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_mesh3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_mesh3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_mesh3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gpu Mesh3d Specification

## Scenarios

### Stream D: GpuMeshHandle

### invalid sentinel

#### AC-3: invalid() vbuf has id -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = GpuMeshHandle.invalid()
expect(h.vbuf.id).to_equal(-1)
```

</details>

#### AC-3: invalid() ibuf has id -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = GpuMeshHandle.invalid()
expect(h.ibuf.id).to_equal(-1)
```

</details>

#### AC-3: invalid() index_count is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = GpuMeshHandle.invalid()
expect(h.index_count).to_equal(0)
```

</details>

### Stream D: gpu_mesh_upload

### upload triangle mesh via software backend

#### AC-3: vbuf id is valid (not -1)

1. var backend = make software backend inited


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_triangle_vertices()
val idxs = make_triangle_indices()
val handle = gpu_mesh_upload(backend, verts, idxs)
expect(handle.vbuf.id).to_be_greater_than(-1)
```

</details>

#### AC-3: ibuf id is valid (not -1)

1. var backend = make software backend inited


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_triangle_vertices()
val idxs = make_triangle_indices()
val handle = gpu_mesh_upload(backend, verts, idxs)
expect(handle.ibuf.id).to_be_greater_than(-1)
```

</details>

#### AC-3: index_count equals number of indices for triangle

1. var backend = make software backend inited
   - Expected: handle.index_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_triangle_vertices()
val idxs = make_triangle_indices()
val handle = gpu_mesh_upload(backend, verts, idxs)
expect(handle.index_count).to_equal(3)
```

</details>

### upload quad mesh via software backend

#### AC-3: index_count equals 6 for quad (two triangles)

1. var backend = make software backend inited
   - Expected: handle.index_count equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_quad_vertices()
val idxs = make_quad_indices()
val handle = gpu_mesh_upload(backend, verts, idxs)
expect(handle.index_count).to_equal(6)
```

</details>

#### AC-3: vbuf and ibuf are distinct handles

1. var backend = make software backend inited
   - Expected: distinct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_quad_vertices()
val idxs = make_quad_indices()
val handle = gpu_mesh_upload(backend, verts, idxs)
val distinct = handle.vbuf.id != handle.ibuf.id
expect(distinct).to_equal(true)
```

</details>

### Stream D: gpu_mesh_draw

### draw calls correct sequence via software backend

#### AC-3: gpu_mesh_draw does not crash with valid mesh and rph

1. var backend = make software backend inited
2. backend begin frame
3. gpu mesh draw
   - Expected: backend.active_pass.pipeline_id equals `pip.id`
   - Expected: backend.active_pass.vertex_buf_id equals `mesh.vbuf.id`
   - Expected: backend.active_pass.index_buf_id equals `mesh.ibuf.id`
4. backend end render pass
5. backend end frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_triangle_vertices()
val idxs = make_triangle_indices()
val mesh = gpu_mesh_upload(backend, verts, idxs)
backend.begin_frame()
val rph = make_render_pass(backend)
val desc = make_pipeline_desc()
val pip = backend.create_pipeline(desc)
val mvp_buf = backend.create_uniform_buffer(64)
gpu_mesh_draw(backend, rph, mesh, mvp_buf, pip)
expect(backend.active_pass.pipeline_id).to_equal(pip.id)
expect(backend.active_pass.vertex_buf_id).to_equal(mesh.vbuf.id)
expect(backend.active_pass.index_buf_id).to_equal(mesh.ibuf.id)
backend.end_render_pass(rph)
backend.end_frame()
```

</details>

#### AC-3: two consecutive mesh draw calls in one frame do not crash

1. var backend = make software backend inited
2. backend begin frame
3. gpu mesh draw
4. gpu mesh draw
   - Expected: backend.active_pass.pipeline_id equals `pip.id`
   - Expected: backend.active_pass.vertex_buf_id equals `mesh2.vbuf.id`
   - Expected: backend.active_pass.index_buf_id equals `mesh2.ibuf.id`
5. backend end render pass
6. backend end frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_triangle_vertices()
val idxs = make_triangle_indices()
val mesh1 = gpu_mesh_upload(backend, verts, idxs)
val mesh2 = gpu_mesh_upload(backend, verts, idxs)
backend.begin_frame()
val rph = make_render_pass(backend)
val desc = make_pipeline_desc()
val pip = backend.create_pipeline(desc)
val mvp_buf = backend.create_uniform_buffer(64)
gpu_mesh_draw(backend, rph, mesh1, mvp_buf, pip)
gpu_mesh_draw(backend, rph, mesh2, mvp_buf, pip)
expect(backend.active_pass.pipeline_id).to_equal(pip.id)
expect(backend.active_pass.vertex_buf_id).to_equal(mesh2.vbuf.id)
expect(backend.active_pass.index_buf_id).to_equal(mesh2.ibuf.id)
backend.end_render_pass(rph)
backend.end_frame()
```

</details>

### Stream D: gpu_mesh_free

### free marks handles invalid

#### AC-3: after free, vbuf id is -1

1. var backend = make software backend inited
2. var handle = gpu mesh upload
3. gpu mesh free
   - Expected: handle.vbuf.id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_triangle_vertices()
val idxs = make_triangle_indices()
var handle = gpu_mesh_upload(backend, verts, idxs)
gpu_mesh_free(handle)
expect(handle.vbuf.id).to_equal(-1)
```

</details>

#### AC-3: after free, ibuf id is -1

1. var backend = make software backend inited
2. var handle = gpu mesh upload
3. gpu mesh free
   - Expected: handle.ibuf.id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val verts = make_triangle_vertices()
val idxs = make_triangle_indices()
var handle = gpu_mesh_upload(backend, verts, idxs)
gpu_mesh_free(handle)
expect(handle.ibuf.id).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/gpu_mesh3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stream D: GpuMeshHandle
- invalid sentinel
- Stream D: gpu_mesh_upload
- upload triangle mesh via software backend
- upload quad mesh via software backend
- Stream D: gpu_mesh_draw
- draw calls correct sequence via software backend
- Stream D: gpu_mesh_free
- free marks handles invalid

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
