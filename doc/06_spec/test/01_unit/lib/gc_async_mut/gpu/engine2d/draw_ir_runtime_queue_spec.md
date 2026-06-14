# Engine2D Draw IR Runtime Queue Spec

> This focused spec covers the production bridge from a GPU-selected Draw IR

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

This focused spec covers the production bridge from a GPU-selected Draw IR

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

This focused spec covers the production bridge from a GPU-selected Draw IR
batch into the host/GPU runtime queue. It intentionally avoids SGTTI and broad
browser imports so native verification stays scoped to Engine2D, Draw IR, and
the runtime queue API.

## Scenarios

### Engine2D Draw IR runtime queue bridge

#### submits and drains a GPU-selected Draw IR batch through the runtime queue

- rt host gpu queue reset
- var engine = Engine2D create with backend
- engine clear
- draw ir rect
   - Expected: result.render.unit_id equals `batch-runtime`
   - Expected: result.render.selected_backend equals `gpu`
   - Expected: result.render.rendered_command_count equals `1`
   - Expected: result.runtime_submit.packet_id equals `1`
   - Expected: result.runtime_drain.drained equals `1`
   - Expected: result.runtime_drain.status equals `completed`
   - Expected: result.render.pixels[3 * 32 + 2] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_host_gpu_queue_reset()
var engine = Engine2D.create_with_backend(32, 24, "cpu")
engine.clear(BG)
val batch = draw_ir_batch("batch-runtime", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 0, 0, 20, 16, 10, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val queue = engine2d_host_gpu_runtime_queue("vulkan", 7, true, 4096)

val result = engine2d_draw_ir_adv_batch_runtime_queue(engine, batch, true, queue)

expect(result.render.unit_id).to_equal("batch-runtime")
expect(result.render.selected_backend).to_equal("gpu")
expect(result.render.rendered_command_count).to_equal(1)
expect(result.runtime_submit.submitted).to_be(true)
expect(result.runtime_submit.packet_id).to_equal(1)
expect(result.runtime_drain.drained).to_equal(1)
expect(result.runtime_drain.status).to_equal("completed")
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


</details>
