# Simple2D WebGPU Surface Bounds Spec

> The browser-hosted Simple2D path can submit canvas commands into the in-repo WebGPU facade. Oversized dimensions must fail closed before context/device setup so synthetic WebGPU evidence cannot claim a backend submission for a surface that the shared web rendering lane rejects elsewhere.

<!-- sdn-diagram:id=simple2d_webgpu_surface_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple2d_webgpu_surface_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple2d_webgpu_surface_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple2d_webgpu_surface_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple2D WebGPU Surface Bounds Spec

The browser-hosted Simple2D path can submit canvas commands into the in-repo WebGPU facade. Oversized dimensions must fail closed before context/device setup so synthetic WebGPU evidence cannot claim a backend submission for a surface that the shared web rendering lane rejects elsewhere.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple2d_webgpu_surface_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The browser-hosted Simple2D path can submit canvas commands into the in-repo
WebGPU facade. Oversized dimensions must fail closed before context/device
setup so synthetic WebGPU evidence cannot claim a backend submission for a
surface that the shared web rendering lane rejects elsewhere.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct evidence-field assertions.

## Scenarios

### Simple2D WebGPU surface bounds hardening

#### rejects oversized Simple2D WebGPU surfaces before queue submission

- var simple2d = canvas get context simple2d
- simple2d fill rect
   - Expected: evidence.status equals `webgpu-surface-size-invalid`
   - Expected: evidence.command_count equals `1`
   - Expected: evidence.queue_write_count equals `0`
   - Expected: evidence.render_pass_count equals `0`
   - Expected: evidence.draw_call_count equals `0`
   - Expected: evidence.present_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var simple2d = canvas_get_context_simple2d(4096, 4097)
simple2d.fill_rect(1, 1, 8, 8, 0xFF336699)

val evidence = simple2d.submit_to_webgpu(true)

expect(evidence.available).to_be(false)
expect(evidence.submitted).to_be(false)
expect(evidence.status).to_equal("webgpu-surface-size-invalid")
expect(evidence.command_count).to_equal(1)
expect(evidence.queue_write_count).to_equal(0)
expect(evidence.render_pass_count).to_equal(0)
expect(evidence.draw_call_count).to_equal(0)
expect(evidence.present_count).to_equal(0)
expect(evidence.pipeline_valid).to_be(false)
expect(evidence.canvas2d_json).to_contain("\"op\":\"fillRect\"")
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
