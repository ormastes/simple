# WebGPU Shader Source Bounds Spec

> Browser JavaScript, WASM, Simple2D, and Simple3D paths share shader module creation. Invalid shader source must not produce a handle that later pipeline creation can mistake for admitted backend work.

<!-- sdn-diagram:id=webgpu_shader_source_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_shader_source_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_shader_source_bounds_spec -> std
webgpu_shader_source_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_shader_source_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WebGPU Shader Source Bounds Spec

Browser JavaScript, WASM, Simple2D, and Simple3D paths share shader module creation. Invalid shader source must not produce a handle that later pipeline creation can mistake for admitted backend work.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/webgpu_shader_source_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Browser JavaScript, WASM, Simple2D, and Simple3D paths share shader module
creation. Invalid shader source must not produce a handle that later pipeline
creation can mistake for admitted backend work.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct shader id/state assertions.

## Scenarios

### browser WebGPU shader source bounds hardening

#### rejects empty and oversized shader sources without advancing ids

- var gpu ctx = webgpu create context
   - Expected: empty_shader.id equals `-1`
   - Expected: gpu_ctx.next_shader_id equals `1`
   - Expected: oversized_shader.id equals `-1`
   - Expected: gpu_ctx.next_shader_id equals `1`
   - Expected: valid_shader.id equals `1`
   - Expected: gpu_ctx.next_shader_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gpu_ctx = webgpu_create_context(true)
val requested = gpu_ctx.request_device()
expect(requested).to_be(true)

val empty_shader = gpu_ctx.create_shader_module("empty", "")
expect(empty_shader.id).to_equal(-1)
expect(empty_shader.valid).to_be(false)
expect(gpu_ctx.next_shader_id).to_equal(1)

val oversized_shader = gpu_ctx.create_shader_module("oversized", str_repeat("@compute fn main() {}\n", 206))
expect(oversized_shader.id).to_equal(-1)
expect(oversized_shader.valid).to_be(false)
expect(gpu_ctx.next_shader_id).to_equal(1)

val valid_shader = gpu_ctx.create_shader_module("valid", "@compute @workgroup_size(1) fn main() { }")
expect(valid_shader.id).to_equal(1)
expect(valid_shader.valid).to_be(true)
expect(gpu_ctx.next_shader_id).to_equal(2)
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
