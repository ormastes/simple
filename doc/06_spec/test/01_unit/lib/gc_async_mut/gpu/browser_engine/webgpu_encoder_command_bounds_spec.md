# WebGPU Encoder Command Bounds Spec

> The browser WebGPU facade is shared by JavaScript, WASM, Simple2D, and Simple3D evidence paths. Oversized draw or dispatch commands must invalidate the command buffer so queue submission cannot treat them as successful backend work.

<!-- sdn-diagram:id=webgpu_encoder_command_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_encoder_command_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_encoder_command_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_encoder_command_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WebGPU Encoder Command Bounds Spec

The browser WebGPU facade is shared by JavaScript, WASM, Simple2D, and Simple3D evidence paths. Oversized draw or dispatch commands must invalidate the command buffer so queue submission cannot treat them as successful backend work.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/webgpu_encoder_command_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The browser WebGPU facade is shared by JavaScript, WASM, Simple2D, and Simple3D
evidence paths. Oversized draw or dispatch commands must invalidate the command
buffer so queue submission cannot treat them as successful backend work.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct command encoder assertions.

## Scenarios

### browser WebGPU encoder command bounds hardening

#### rejects oversized draw commands before queue submission

- var gpu ctx = webgpu create context
- var encoder = gpu ctx create command encoder
   - Expected: encoder.draw_call_count equals `0`
   - Expected: gpu_ctx.queue.submitted.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gpu_ctx = webgpu_create_context(true)
val requested = gpu_ctx.request_device()
expect(requested).to_be(true)

var encoder = gpu_ctx.create_command_encoder("oversized-draw")
val began = encoder.begin_render_pass()
expect(began).to_be(true)

val drawn = encoder.draw(1048577, 1)
expect(drawn).to_be(false)
expect(encoder.draw_call_count).to_equal(0)

val command_buffer = encoder.finish("oversized-draw-commands")
expect(command_buffer.valid).to_be(false)
val submitted = gpu_ctx.queue_submit([command_buffer])
expect(submitted).to_be(false)
expect(gpu_ctx.queue.submitted.len()).to_equal(0)
```

</details>

#### rejects oversized dispatch commands before queue submission

- var gpu ctx = webgpu create context
- var encoder = gpu ctx create command encoder
   - Expected: encoder.dispatched_workgroups equals `0`
   - Expected: gpu_ctx.queue.submitted.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gpu_ctx = webgpu_create_context(true)
val requested = gpu_ctx.request_device()
expect(requested).to_be(true)

var encoder = gpu_ctx.create_command_encoder("oversized-dispatch")
val began = encoder.begin_compute_pass()
expect(began).to_be(true)

val dispatched = encoder.dispatch_workgroups(1025, 1025, 1)
expect(dispatched).to_be(false)
expect(encoder.dispatched_workgroups).to_equal(0)

val command_buffer = encoder.finish("oversized-dispatch-commands")
expect(command_buffer.valid).to_be(false)
val submitted = gpu_ctx.queue_submit([command_buffer])
expect(submitted).to_be(false)
expect(gpu_ctx.queue.submitted.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
