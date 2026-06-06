# Graph Ir3d Specification

> 1. var graph = GraphIr3D new

<!-- sdn-diagram:id=graph_ir3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=graph_ir3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

graph_ir3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=graph_ir3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Graph Ir3d Specification

## Scenarios

### Graph IR 3D

### REQ-3D-GRAPH-001: records backend-neutral 3D passes and draws

#### tracks pass, draw, and deduped resource counts

1. var graph = GraphIr3D new

2. graph add draw

3. graph add draw
   - Expected: stats.pass_count equals `1`
   - Expected: stats.draw_count equals `2`
   - Expected: stats.resource_count equals `6`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = GraphIr3D.new()
val pass_id = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
val mesh = mesh_handle(10, 11, 6)
graph.add_draw(pass_id, mesh, BufferHandle(id: 12), PipelineHandle(id: 20))
graph.add_draw(pass_id, mesh, BufferHandle(id: 12), PipelineHandle(id: 20))

val stats = graph.stats()
expect(stats.pass_count).to_equal(1)
expect(stats.draw_count).to_equal(2)
expect(stats.resource_count).to_equal(6)
```

</details>

#### ignores invalid mesh and pipeline handles

1. var graph = GraphIr3D new

2. graph add draw

3. graph add draw
   - Expected: graph.stats().draw_count equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = GraphIr3D.new()
val pass_id = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
graph.add_draw(pass_id, GpuMeshHandle.invalid(), BufferHandle(id: 12), PipelineHandle(id: 20))
graph.add_draw(pass_id, mesh_handle(10, 11, 6), BufferHandle(id: 12), PipelineHandle.invalid())

expect(graph.stats().draw_count).to_equal(0)
```

</details>

### REQ-3D-GRAPH-002: optimizes draw order for 3D backend state locality

#### sorts draws inside each pass by pipeline then texture then mesh

1. var graph = GraphIr3D new

2. graph add textured draw

3. graph add textured draw

4. graph add textured draw
   - Expected: optimized.draws[0].pipeline_id equals `3`
   - Expected: optimized.draws[0].texture_id equals `4`
   - Expected: optimized.draws[1].pipeline_id equals `3`
   - Expected: optimized.draws[1].texture_id equals `5`
   - Expected: optimized.draws[2].pipeline_id equals `9`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = GraphIr3D.new()
val pass_id = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
graph.add_textured_draw(pass_id, mesh_handle(30, 31, 3), BufferHandle(id: 80), TextureHandle(id: 6), PipelineHandle(id: 9))
graph.add_textured_draw(pass_id, mesh_handle(10, 11, 3), BufferHandle(id: 81), TextureHandle(id: 4), PipelineHandle(id: 3))
graph.add_textured_draw(pass_id, mesh_handle(20, 21, 3), BufferHandle(id: 82), TextureHandle(id: 5), PipelineHandle(id: 3))

val optimized = graph_ir3d_optimize_for_3d(graph)

expect(optimized.draws[0].pipeline_id).to_equal(3)
expect(optimized.draws[0].texture_id).to_equal(4)
expect(optimized.draws[1].pipeline_id).to_equal(3)
expect(optimized.draws[1].texture_id).to_equal(5)
expect(optimized.draws[2].pipeline_id).to_equal(9)
```

</details>

#### preserves pass boundaries while batching

1. var graph = GraphIr3D new

2. graph add draw

3. graph add draw
   - Expected: optimized.passes.len() equals `2`
   - Expected: optimized.passes[0].draw_count equals `1`
   - Expected: optimized.passes[1].draw_count equals `1`
   - Expected: optimized.draws[0].pass_id equals `optimized.passes[0].id`
   - Expected: optimized.draws[1].pass_id equals `optimized.passes[1].id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var graph = GraphIr3D.new()
val first = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
val second = graph.begin_pass(TextureHandle(id: 3), TextureHandle(id: 4))
graph.add_draw(first, mesh_handle(30, 31, 3), BufferHandle(id: 80), PipelineHandle(id: 9))
graph.add_draw(second, mesh_handle(10, 11, 3), BufferHandle(id: 81), PipelineHandle(id: 3))

val optimized = graph_ir3d_optimize_for_3d(graph)

expect(optimized.passes.len()).to_equal(2)
expect(optimized.passes[0].draw_count).to_equal(1)
expect(optimized.passes[1].draw_count).to_equal(1)
expect(optimized.draws[0].pass_id).to_equal(optimized.passes[0].id)
expect(optimized.draws[1].pass_id).to_equal(optimized.passes[1].id)
```

</details>

### REQ-3D-GRAPH-003: replays optimized graph through RenderBackend3D

#### executes graph draws through a RenderBackend3D implementation

1. var backend = RecordingRenderBackend3D create

2. var graph = GraphIr3D new

3. graph add draw

4. graph ir3d execute
   - Expected: backend.begin_frame_count equals `1`
   - Expected: backend.begin_pass_count equals `1`
   - Expected: backend.set_pipeline_count equals `1`
   - Expected: backend.bind_vertex_count equals `1`
   - Expected: backend.bind_index_count equals `1`
   - Expected: backend.bind_uniform_count equals `1`
   - Expected: backend.draw_count equals `1`
   - Expected: backend.end_pass_count equals `1`
   - Expected: backend.end_frame_count equals `1`
   - Expected: backend.last_pipeline_id equals `pipeline.id`
   - Expected: backend.last_vbuf_id equals `vbuf.id`
   - Expected: backend.last_ibuf_id equals `ibuf.id`
   - Expected: backend.last_uniform_id equals `uniform.id`
   - Expected: backend.last_index_count equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = RecordingRenderBackend3D.create()
val color = backend.create_texture(16, 16, TextureFormat3D.Rgba8Unorm)
val depth = backend.create_texture(16, 16, TextureFormat3D.Depth32Float)
val vbuf = backend.create_vertex_buffer(96)
val ibuf = backend.create_index_buffer(12)
val uniform = backend.create_uniform_buffer(64)
val pipeline = backend.create_pipeline(PipelineDesc3D(
    vertex_shader_spirv: [],
    fragment_shader_spirv: [],
    vertex_shader_wgsl: "",
    fragment_shader_wgsl: "",
    vertex_stride: 96,
    cull_back_faces: true,
    depth_write: true,
    depth_test: true
))

var graph = GraphIr3D.new()
val pass_id = graph.begin_pass(color, depth)
graph.add_draw(pass_id, mesh_handle(vbuf.id, ibuf.id, 3), uniform, pipeline)
val optimized = graph_ir3d_optimize_for_3d(graph)
graph_ir3d_execute(backend, optimized)

expect(backend.begin_frame_count).to_equal(1)
expect(backend.begin_pass_count).to_equal(1)
expect(backend.set_pipeline_count).to_equal(1)
expect(backend.bind_vertex_count).to_equal(1)
expect(backend.bind_index_count).to_equal(1)
expect(backend.bind_uniform_count).to_equal(1)
expect(backend.draw_count).to_equal(1)
expect(backend.end_pass_count).to_equal(1)
expect(backend.end_frame_count).to_equal(1)
expect(backend.last_pipeline_id).to_equal(pipeline.id)
expect(backend.last_vbuf_id).to_equal(vbuf.id)
expect(backend.last_ibuf_id).to_equal(ibuf.id)
expect(backend.last_uniform_id).to_equal(uniform.id)
expect(backend.last_index_count).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Graph IR 3D
- REQ-3D-GRAPH-001: records backend-neutral 3D passes and draws
- REQ-3D-GRAPH-002: optimizes draw order for 3D backend state locality
- REQ-3D-GRAPH-003: replays optimized graph through RenderBackend3D

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
