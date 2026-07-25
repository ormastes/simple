# GPU / Draw / Event Intensive Tests — TL;DR

Near-100% branch coverage of GPU processing, 2D drawing, and UI events via SSpec.
Shared portable bodies (Linux CI) + system-specific device checkpoints
(fail-closed `host-unavailable`, never silent skip).

```sdn
plan:
  portable_shared: [kernel-emission, payload-gating(no/match/corrupt),
                    exec-target suggest/require, scheduler-state-machine,
                    cpu-sw per-primitive readback, draw-ir item-dispatch,
                    hit-test semantics, cpu<->gpu queue round-trip]
  system_specific: [metal(macOS), vulkan(device), cuda/hip(device), directx(win)]
  matrix: {processing: [vulkan, metal, cuda, hip]} x {drawing: [metal, vulkan, directx]}
  feature: gpu-scheduler debug-log via std.diag (dbg_event_hop/stage/provenance,
           SIMPLE_DIAG=events,stage) at host_gpu_event_queue + draw_ir_runtime_queue
  ui_draw_fixes: [vulkan empty-shader trio, metal clip no-op]
  oracle: read_pixels()->PPM + provenance flags (no false-green parity)
```

Honest baseline: compute stack = payload-gated simulation (real device only
proven on Metal); Vulkan line/circle_outline/rounded_rect = empty shader;
`std.diag` complete but wired nowhere. Full plan: `gpu_draw_event_intensive_tests.md`.
