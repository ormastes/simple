# No-GC Engine2D Draw IR Runtime Queue Spec

> This focused spec covers the no-GC Draw IR queue-dispatch helper. It proves payload checksum/SDN text generation and runtime submit/drain/dispatch receipts without importing the GC Engine2D renderer.

<!-- sdn-diagram:id=draw_ir_runtime_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_runtime_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_runtime_queue_spec -> std
draw_ir_runtime_queue_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_runtime_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# No-GC Engine2D Draw IR Runtime Queue Spec

This focused spec covers the no-GC Draw IR queue-dispatch helper. It proves payload checksum/SDN text generation and runtime submit/drain/dispatch receipts without importing the GC Engine2D renderer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused spec covers the no-GC Draw IR queue-dispatch helper. It proves
payload checksum/SDN text generation and runtime submit/drain/dispatch receipts
without importing the GC Engine2D renderer.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md

## Syntax

The no-GC dispatch helper is imported directly from
`std.nogc_async_mut.gpu.engine2d.draw_ir_runtime_queue`. The queue identity
comes from `engine2d_host_gpu_runtime_queue_with_backend_handle`, and the test
uses only built-in SSpec matchers.

## Examples

```simple
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val result = engine2d_draw_ir_runtime_queue_dispatch_only(batch, true, queue)
expect(result.runtime_dispatch.backend_handle).to_equal(7)
```

## Acceptance

The scenario builds a GPU-selected Draw IR batch, submits it through the no-GC
runtime queue helper, and asserts that the runtime receipt carries the backend
handle, payload hash, and Draw IR v2 payload text.

## Scenarios

### no-GC Engine2D Draw IR runtime queue dispatch

#### submits and dispatches a GPU-selected Draw IR payload without GC Engine2D

- rt host gpu queue reset
- draw ir rect
   - Expected: result.payload.batch_id equals `nogc-runtime`
   - Expected: result.payload.command_count equals `1`
   - Expected: result.runtime_submit.packet_id equals `1`
   - Expected: result.runtime_drain.drained equals `1`
   - Expected: result.runtime_drain.status equals `completed`
   - Expected: result.runtime_drain.last_backend_handle equals `7`
   - Expected: result.runtime_dispatch.status equals `dispatched`
   - Expected: result.runtime_dispatch.backend_handle equals `7`
   - Expected: result.runtime_dispatch.payload_hash equals `result.payload.command_checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_host_gpu_queue_reset()
val batch = draw_ir_batch("nogc-runtime", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 0, 0, 20, 16, 10, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)

val result = engine2d_draw_ir_runtime_queue_dispatch_only(batch, true, queue)

expect(result.payload.batch_id).to_equal("nogc-runtime")
expect(result.payload.command_count).to_equal(1)
expect(result.runtime_submit.submitted).to_be(true)
expect(result.runtime_submit.packet_id).to_equal(1)
expect(result.runtime_drain.drained).to_equal(1)
expect(result.runtime_drain.status).to_equal("completed")
expect(result.runtime_drain.last_backend_handle).to_equal(7)
expect(result.runtime_dispatch.dispatched).to_be(true)
expect(result.runtime_dispatch.status).to_equal("dispatched")
expect(result.runtime_dispatch.backend_handle).to_equal(7)
expect(result.runtime_dispatch.payload_hash).to_equal(result.payload.command_checksum)
expect(result.runtime_dispatch.payload_text).to_contain("schema=simple-draw-ir-v2")
expect(result.queued_for_gpu).to_be(true)
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

- **Plan:** [doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md](doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
