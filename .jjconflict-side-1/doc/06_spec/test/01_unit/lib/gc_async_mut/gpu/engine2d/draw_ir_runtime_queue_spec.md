# Engine2D Draw IR Runtime Queue Spec

> This focused spec covers the production bridge from a GPU-selected Draw IR batch into the host/GPU runtime queue. It intentionally avoids SGTTI and broad browser imports so native verification stays scoped to Engine2D, Draw IR, and the runtime queue API.

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

# Engine2D Draw IR Runtime Queue Spec

This focused spec covers the production bridge from a GPU-selected Draw IR batch into the host/GPU runtime queue. It intentionally avoids SGTTI and broad browser imports so native verification stays scoped to Engine2D, Draw IR, and the runtime queue API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused spec covers the production bridge from a GPU-selected Draw IR
batch into the host/GPU runtime queue. It intentionally avoids SGTTI and broad
browser imports so native verification stays scoped to Engine2D, Draw IR, and
the runtime queue API.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

The scenario creates a Draw IR batch that requests the GPU backend, submits it
through an Engine2D host/GPU runtime queue with queue identity `1` and backend
handle `7`, renders the batch, drains the runtime queue, and asserts that the
runtime drain reports the backend handle rather than the queue id.

## Scenarios

### Engine2D Draw IR runtime queue bridge

#### submits and drains a GPU-selected Draw IR batch through the runtime queue

- engine2d host gpu runtime reset
- var engine = Engine2D create with backend
- engine clear
- draw ir rect
   - Expected: result.render.unit_id equals `runtime-batch-runtime`
   - Expected: result.render.selected_backend equals `gpu`
   - Expected: result.render.rendered_command_count equals `1`
   - Expected: result.runtime_submit.packet_id equals `1`
   - Expected: result.runtime_drain.drained equals `1`
   - Expected: result.runtime_drain.status equals `completed`
   - Expected: result.runtime_drain.queue_handle equals `1`
   - Expected: result.runtime_drain.last_backend_handle equals `7`
   - Expected: result.render.pixels[3 * 32 + 2] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
engine2d_host_gpu_runtime_reset()
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("batch-runtime", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 0, 0, 20, 16, 10, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)

val result = engine2d_draw_ir_adv_batch_runtime_queue(engine, batch, true, queue)

# Runtime-queued batches dispatch through a "runtime-"-tagged composition
# (see draw_ir_runtime_queue.spl payload summary), so the rendered unit id
# reflects that composition id, not the bare batch id.
expect(result.render.unit_id).to_equal("runtime-batch-runtime")
expect(result.render.selected_backend).to_equal("gpu")
expect(result.render.rendered_command_count).to_equal(1)
expect(result.runtime_submit.submitted).to_be(true)
expect(result.runtime_submit.packet_id).to_equal(1)
expect(result.runtime_drain.drained).to_equal(1)
expect(result.runtime_drain.status).to_equal("completed")
expect(result.runtime_drain.queue_handle).to_equal(1)
expect(result.runtime_drain.last_backend_handle).to_equal(7)
expect(result.queued_for_gpu).to_be(true)
expect(result.render.pixels[3 * 32 + 2]).to_equal(GREEN)
engine.shutdown()
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

- **Plan:** [doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md](doc/03_plan/agent_tasks/real_host_gpu_runtime_queue_emission.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
