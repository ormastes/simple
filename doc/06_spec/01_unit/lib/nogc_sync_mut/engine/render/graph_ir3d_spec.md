# graph_ir3d_spec

> Verifies the graph ir3d behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# graph_ir3d_spec

Verifies the graph ir3d behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the graph ir3d behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Graph IR 3D

### REQ-3D-GRAPH-001: records backend-neutral 3D passes and draws

#### tracks pass, draw, and deduped resource counts

- Verify: tracks pass, draw, and deduped resource counts
   - Expected: stats.pass_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: stats.draw_count equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: stats.resource_count equals `6)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3D-GRAPH-001 REQ-3D-GRAPH-002 REQ-3D-GRAPH-003
step("Verify: tracks pass, draw, and deduped resource counts")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var graph = GraphIr3D.new()
val pass_id = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
val mesh = mesh_handle(10, 11, 6)
graph.add_draw(pass_id, mesh, BufferHandle(id: 12), PipelineHandle(id: 20))
graph.add_draw(pass_id, mesh, BufferHandle(id: 12), PipelineHandle(id: 20))

val stats = graph.stats()
expect(stats.pass_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(stats.draw_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(stats.resource_count).to_equal(6)  # oracle: pinned constant asserted by this scenario
```

</details>

#### ignores invalid mesh and pipeline handles

- Verify: ignores invalid mesh and pipeline handles
   - Expected: graph.stats().draw_count equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3D-GRAPH-001 REQ-3D-GRAPH-002 REQ-3D-GRAPH-003
step("Verify: ignores invalid mesh and pipeline handles")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var graph = GraphIr3D.new()
val pass_id = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
graph.add_draw(pass_id, GpuMeshHandle.invalid(), BufferHandle(id: 12), PipelineHandle(id: 20))
graph.add_draw(pass_id, mesh_handle(10, 11, 6), BufferHandle(id: 12), PipelineHandle.invalid())

expect(graph.stats().draw_count).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### REQ-3D-GRAPH-002: optimizes draw order for 3D backend state locality

#### sorts draws inside each pass by pipeline then texture then mesh

- Verify: sorts draws inside each pass by pipeline then texture then mesh
   - Expected: optimized.draws[0].pipeline_id equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: optimized.draws[0].texture_id equals `4)  # oracle: pinned constant asserted by this scenario`
   - Expected: optimized.draws[1].pipeline_id equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: optimized.draws[1].texture_id equals `5)  # oracle: pinned constant asserted by this scenario`
   - Expected: optimized.draws[2].pipeline_id equals `9)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3D-GRAPH-001 REQ-3D-GRAPH-002 REQ-3D-GRAPH-003
step("Verify: sorts draws inside each pass by pipeline then texture then mesh")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var graph = GraphIr3D.new()
val pass_id = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
graph.add_textured_draw(pass_id, mesh_handle(30, 31, 3), BufferHandle(id: 80), TextureHandle(id: 6), PipelineHandle(id: 9))
graph.add_textured_draw(pass_id, mesh_handle(10, 11, 3), BufferHandle(id: 81), TextureHandle(id: 4), PipelineHandle(id: 3))
graph.add_textured_draw(pass_id, mesh_handle(20, 21, 3), BufferHandle(id: 82), TextureHandle(id: 5), PipelineHandle(id: 3))

val optimized = graph_ir3d_optimize_for_3d(graph)

expect(optimized.draws[0].pipeline_id).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(optimized.draws[0].texture_id).to_equal(4)  # oracle: pinned constant asserted by this scenario
expect(optimized.draws[1].pipeline_id).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(optimized.draws[1].texture_id).to_equal(5)  # oracle: pinned constant asserted by this scenario
expect(optimized.draws[2].pipeline_id).to_equal(9)  # oracle: pinned constant asserted by this scenario
```

</details>

#### preserves pass boundaries while batching

- Verify: preserves pass boundaries while batching
   - Expected: optimized.passes.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: optimized.passes[0].draw_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: optimized.passes[1].draw_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: optimized.draws[0].pass_id equals `optimized.passes[0].id`
   - Expected: optimized.draws[1].pass_id equals `optimized.passes[1].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3D-GRAPH-001 REQ-3D-GRAPH-002 REQ-3D-GRAPH-003
step("Verify: preserves pass boundaries while batching")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var graph = GraphIr3D.new()
val first = graph.begin_pass(TextureHandle(id: 1), TextureHandle(id: 2))
val second = graph.begin_pass(TextureHandle(id: 3), TextureHandle(id: 4))
graph.add_draw(first, mesh_handle(30, 31, 3), BufferHandle(id: 80), PipelineHandle(id: 9))
graph.add_draw(second, mesh_handle(10, 11, 3), BufferHandle(id: 81), PipelineHandle(id: 3))

val optimized = graph_ir3d_optimize_for_3d(graph)

expect(optimized.passes.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(optimized.passes[0].draw_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(optimized.passes[1].draw_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(optimized.draws[0].pass_id).to_equal(optimized.passes[0].id)
expect(optimized.draws[1].pass_id).to_equal(optimized.passes[1].id)
```

</details>

### REQ-3D-GRAPH-003: replays optimized graph through RenderBackend3D

#### executes graph draws through a RenderBackend3D implementation

- Verify: executes graph draws through a RenderBackend3D implementation
   - Expected: backend.begin_frame_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.begin_pass_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.set_pipeline_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.bind_vertex_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.bind_index_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.bind_uniform_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.draw_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.end_pass_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.end_frame_count equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: backend.last_pipeline_id equals `pipeline.id`
   - Expected: backend.last_vbuf_id equals `vbuf.id`
   - Expected: backend.last_ibuf_id equals `ibuf.id`
   - Expected: backend.last_uniform_id equals `uniform.id`
   - Expected: backend.last_index_count equals `3)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3D-GRAPH-001 REQ-3D-GRAPH-002 REQ-3D-GRAPH-003
step("Verify: executes graph draws through a RenderBackend3D implementation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

expect(backend.begin_frame_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.begin_pass_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.set_pipeline_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.bind_vertex_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.bind_index_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.bind_uniform_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.draw_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.end_pass_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.end_frame_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(backend.last_pipeline_id).to_equal(pipeline.id)
expect(backend.last_vbuf_id).to_equal(vbuf.id)
expect(backend.last_ibuf_id).to_equal(ibuf.id)
expect(backend.last_uniform_id).to_equal(uniform.id)
expect(backend.last_index_count).to_equal(3)  # oracle: pinned constant asserted by this scenario
```

</details>

#### executes graph draws through the software 3D backend

- Verify: executes graph draws through the software 3D backend
   - Expected: backend.renderer.get_stats().draw_calls equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-3D-GRAPH-001 REQ-3D-GRAPH-002 REQ-3D-GRAPH-003
step("Verify: executes graph draws through the software 3D backend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var backend = SoftwareRenderBackend3D.create()
val _ = backend.init(16, 16)
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
graph_ir3d_execute(backend, graph_ir3d_optimize_for_3d(graph))

expect(backend.renderer.get_stats().draw_calls).to_equal(1)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee8672806088aade324d8c579f81445f758ce4f1f1ab28cf5af0ff2c794b0ba6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee8672806088aade324d8c579f81445f758ce4f1f1ab28cf5af0ff2c794b0ba6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee8672806088aade324d8c579f81445f758ce4f1f1ab28cf5af0ff2c794b0ba6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/engine/render/graph_ir3d_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
