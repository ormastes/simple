# WebGPU Buffer Allocation Bounds Spec

> JavaScript, WASM, Simple2D, and Simple3D browser paths all share the same WebGPU resource table. Invalid allocation requests must not mint usable buffer ids or advance the resource id sequence.

<!-- sdn-diagram:id=webgpu_buffer_allocation_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_buffer_allocation_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_buffer_allocation_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_buffer_allocation_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WebGPU Buffer Allocation Bounds Spec

JavaScript, WASM, Simple2D, and Simple3D browser paths all share the same WebGPU resource table. Invalid allocation requests must not mint usable buffer ids or advance the resource id sequence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/webgpu_buffer_allocation_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

JavaScript, WASM, Simple2D, and Simple3D browser paths all share the same WebGPU
resource table. Invalid allocation requests must not mint usable buffer ids or
advance the resource id sequence.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct resource table assertions.

## Scenarios

### browser WebGPU buffer allocation bounds hardening

#### rejects invalid buffer sizes without registering usable handles

- var resources = WebGPUResourceTable create
   - Expected: negative.id equals `-1`
   - Expected: resources.buffers.len() equals `0`
   - Expected: resources.next_buffer_id equals `1`
   - Expected: oversized.id equals `-1`
   - Expected: resources.buffers.len() equals `0`
   - Expected: resources.next_buffer_id equals `1`
   - Expected: valid.id equals `1`
   - Expected: resources.buffer_size(valid.id) equals `16`
   - Expected: resources.buffers.len() equals `1`
   - Expected: resources.next_buffer_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()

val negative = resources.create_buffer("negative", -1, WEBGPU_BUFFER_USAGE_COPY_DST_FOR_SPEC)
expect(negative.id).to_equal(-1)
expect(resources.buffer_exists(negative.id)).to_be(false)
expect(resources.buffers.len()).to_equal(0)
expect(resources.next_buffer_id).to_equal(1)

val oversized = resources.create_buffer("oversized", 16777217, WEBGPU_BUFFER_USAGE_COPY_DST_FOR_SPEC)
expect(oversized.id).to_equal(-1)
expect(resources.buffer_exists(oversized.id)).to_be(false)
expect(resources.buffers.len()).to_equal(0)
expect(resources.next_buffer_id).to_equal(1)

val valid = resources.create_buffer("valid", 16, WEBGPU_BUFFER_USAGE_COPY_DST_FOR_SPEC)
expect(valid.id).to_equal(1)
expect(resources.buffer_exists(valid.id)).to_be(true)
expect(resources.buffer_size(valid.id)).to_equal(16)
expect(resources.buffers.len()).to_equal(1)
expect(resources.next_buffer_id).to_equal(2)
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
