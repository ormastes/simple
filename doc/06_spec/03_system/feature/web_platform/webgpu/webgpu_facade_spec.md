# Webgpu Facade Specification

> 1. var resources = WebGPUResourceTable create

<!-- sdn-diagram:id=webgpu_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Facade Specification

## Scenarios

### WebGPU browser engine facade

#### exports sampler layout types through the browser engine facade

1. var resources = WebGPUResourceTable create
   - Expected: nearest_layout_entry.binding_type equals `WEBGPU_BINDING_TYPE_NON_FILTERING_SAMPLER`
   - Expected: comparison_layout_entry.binding_type equals `WEBGPU_BINDING_TYPE_COMPARISON_SAMPLER`
   - Expected: nearest_group.valid is true
   - Expected: comparison_group.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val nearest = resources.create_sampler("nearest", "clamp-to-edge", "clamp-to-edge", "nearest", "nearest")
val comparison = resources.create_sampler_with_descriptor("shadow", "clamp-to-edge", "clamp-to-edge", "clamp-to-edge", "linear", "linear", "linear", 0.0, 32.0, "less-equal", 1)
val nearest_layout_entry = GPUBindGroupLayoutEntry.non_filtering_sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
val comparison_layout_entry = GPUBindGroupLayoutEntry.comparison_sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
val nearest_layout = resources.create_bind_group_layout("nearest", [nearest_layout_entry])
val comparison_layout = resources.create_bind_group_layout("comparison", [comparison_layout_entry])
val nearest_group = resources.create_bind_group("nearest-group", nearest_layout.id, [GPUBindGroupEntry.sampler(0, nearest.id)])
val comparison_group = resources.create_bind_group("comparison-group", comparison_layout.id, [GPUBindGroupEntry.sampler(0, comparison.id)])
expect(nearest_layout_entry.binding_type).to_equal(WEBGPU_BINDING_TYPE_NON_FILTERING_SAMPLER)
expect(comparison_layout_entry.binding_type).to_equal(WEBGPU_BINDING_TYPE_COMPARISON_SAMPLER)
expect(nearest_group.valid).to_equal(true)
expect(comparison_group.valid).to_equal(true)
```

</details>

#### exports depth stencil texture formats through the browser engine facade

1. var resources = WebGPUResourceTable create
   - Expected: depth_stencil.valid is true
   - Expected: depth_stencil.format equals `GPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val depth_stencil = resources.create_texture("depth-stencil", 64, 64, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
expect(depth_stencil.valid).to_equal(true)
expect(depth_stencil.format).to_equal(GPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgpu/webgpu_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebGPU browser engine facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
