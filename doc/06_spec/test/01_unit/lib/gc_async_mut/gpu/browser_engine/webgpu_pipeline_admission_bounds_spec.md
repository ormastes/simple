# WebGPU Pipeline Admission Bounds Spec

> Browser JavaScript, WASM, Simple2D, and Simple3D paths share pipeline creation. Invalid shader handles or device-not-ready state must not consume pipeline ids that can be mistaken for admitted backend work.

<!-- sdn-diagram:id=webgpu_pipeline_admission_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_pipeline_admission_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_pipeline_admission_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_pipeline_admission_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WebGPU Pipeline Admission Bounds Spec

Browser JavaScript, WASM, Simple2D, and Simple3D paths share pipeline creation. Invalid shader handles or device-not-ready state must not consume pipeline ids that can be mistaken for admitted backend work.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/webgpu_pipeline_admission_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Browser JavaScript, WASM, Simple2D, and Simple3D paths share pipeline creation.
Invalid shader handles or device-not-ready state must not consume pipeline ids
that can be mistaken for admitted backend work.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct pipeline id/state assertions.

## Scenarios

### browser WebGPU pipeline admission bounds hardening

#### rejects invalid render and compute pipelines without advancing ids

- var gpu ctx = webgpu create context
   - Expected: not_ready_pipeline.id equals `-1`
   - Expected: gpu_ctx.next_pipeline_id equals `1`
   - Expected: invalid_render.id equals `-1`
   - Expected: gpu_ctx.next_pipeline_id equals `1`
   - Expected: valid_compute.id equals `1`
   - Expected: gpu_ctx.next_pipeline_id equals `2`
   - Expected: valid_render.id equals `2`
   - Expected: gpu_ctx.next_pipeline_id equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gpu_ctx = webgpu_create_context(true)

val not_ready_shader = _invalid_shader("not-ready")
val not_ready_pipeline = gpu_ctx.create_compute_pipeline(not_ready_shader)
expect(not_ready_pipeline.id).to_equal(-1)
expect(not_ready_pipeline.valid).to_be(false)
expect(gpu_ctx.next_pipeline_id).to_equal(1)

val requested = gpu_ctx.request_device()
expect(requested).to_be(true)

val invalid_vertex = _invalid_shader("bad-vs")
val invalid_fragment = _invalid_shader("bad-fs")
val invalid_render = gpu_ctx.create_render_pipeline(invalid_vertex, invalid_fragment)
expect(invalid_render.id).to_equal(-1)
expect(invalid_render.valid).to_be(false)
expect(gpu_ctx.next_pipeline_id).to_equal(1)

val valid_shader = gpu_ctx.create_shader_module("valid", "@compute @workgroup_size(1) fn main() { }")
expect(valid_shader.valid).to_be(true)

val valid_compute = gpu_ctx.create_compute_pipeline(valid_shader)
expect(valid_compute.id).to_equal(1)
expect(valid_compute.valid).to_be(true)
expect(gpu_ctx.next_pipeline_id).to_equal(2)

val valid_render = gpu_ctx.create_render_pipeline(valid_shader, valid_shader)
expect(valid_render.id).to_equal(2)
expect(valid_render.valid).to_be(true)
expect(gpu_ctx.next_pipeline_id).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
