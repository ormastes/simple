# Vulkan Per-Primitive submit_and_wait Caps GUI Render Throughput - 2026-06-18

## Severity
P2 (performance / architecture). Real Vulkan rendering is correct but far too
slow for interactive GUI: a clear-only frame reaches ~219 renders/sec, but any
real widget frame collapses (32 widgets → 7/sec, 128 widgets → 1/sec), missing
the ≥200/sec GUI target by 30–200×.

## Component
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
  - `me clear` (~line 480), `me draw_rect_filled` (~line 494), and every other
    `me draw_*` that calls `vulkan_dispatch_compute`.
- `vulkan_dispatch_compute` (`backend_vulkan_helpers.spl`) — performs the full
  `begin_compute → bind_pipeline → bind_descriptors → push_constants → dispatch
  → end_compute → submit_and_wait` round-trip per call.

## Summary
Each 2D primitive issues an independent, synchronous GPU submission and then
blocks on a fence (`submit_and_wait`) before the next primitive. Measured cost is
~4 ms per draw op under the classic interpreter (interpreter extern overhead +
per-op pipeline bind + queue submit + fence wait). Because a frame is N draw
ops, renders/sec ≈ `1000 / (4 × N)`:

| Frame content          | dispatches | per frame | renders/sec |
|------------------------|-----------:|----------:|------------:|
| clear only             |          1 |   4.5 ms  |     219     |
| clear + 32 widgets     |         33 |   132 ms  |       7     |
| clear + 128 widgets    |        129 |   592 ms  |       1     |

A 200 fps budget (5 ms/frame) therefore only buys ~1 dispatch. The design cannot
hit the target for any non-trivial GUI.

## Reproduce (classic interpreter, Vulkan-capable host)
```bash
SIMPLE_EXECUTION_MODE=interpret bin/simple run <bench.spl>
```
where `<bench.spl>` does `VulkanBackend.create().init(1280,720)` then a timed
loop of `clear` + K `draw_rect_filled` (no `present()`), using
`rt_time_now_unix_micros()`. Throughput drops linearly with K.

## Root cause
Per-primitive synchronous submit. A real GPU submit is normally <100 µs; here
each primitive pays a full command-buffer build + queue submit + fence wait,
multiplied by interpreter extern-call overhead, and serialized (no overlap).

## Proposed fix
Batch a whole frame into ONE command buffer with one submit per frame:
- Record `clear` + all `draw_*` dispatches into a single command buffer
  (memory barriers between dispatches that touch the same framebuffer region).
- One `submit_and_wait` (or fence) per `present()`/frame, not per primitive.
- Optionally keep pipelines/descriptor sets bound across primitives of the same
  kind to cut rebind cost.

Expected effect: per-frame cost approaches `clear + (cheap per-dispatch record)`
rather than `N × 4 ms`, making 200/sec feasible for real widget counts.

## Related
- Readback bottleneck: `vulkan_present_readback_perpixel_simple_loop_2026-06-18`.
- Mode trap (real Vulkan only under classic interpreter; JIT/native stub to 0):
  `rt_vulkan_only_executes_under_classic_interpret_2026-06-17`.
