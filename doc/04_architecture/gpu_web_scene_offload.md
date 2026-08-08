# GPU Web Scene Offload Architecture

## Decision

Adopt a versioned Simple2D GPU event boundary:

`OS input → optional IO → CPU packet forwarder → GPU boundary/hit/event epoch
→ Simple2D DrawIrComposition → Web → GUI → WM`.

The CPU oracle is a peer executor and recovery path, not the permanent owner of
GPU-eligible semantics. Privileged effects remain CPU services and return as
ordinary completion packets.

## Ownership

- OS/IO owns device decoding and privilege.
- The forwarder owns packet normalization, bounded ring publication, required
  cache flush/copy, and submission correlation only.
- `Simple2dGpuEventBoundaryManager` owns eligibility, receipt validation,
  timeout/stale handling, and the single-commit decision.
- The backend owns actual compute dispatch and device-written completion.
- Existing `gpu_web_event_model` is the deterministic CPU oracle.
- Canonical Web/GUI/WM producers consume the resulting semantic scene and emit
  `DrawIrComposition`; transient atlas/cache material stays in Engine2D.

## Existing host implementation and integration seam

The shipped hosted path is already a working CPU implementation, not a missing
feature: `src/os/hosted/hosted_entry.spl` normalizes winit events and calls
`HostCompositor.dispatch_gui_pointer_event`, `dispatch_gui_scroll_event`,
`dispatch_gui_key_event`, and `dispatch_gui_text_event` in
`src/os/compositor/host_compositor_core.spl`. It deliberately reuses
`UISession` primitives rather than the GLFW-only `HostGuiEventRouter`.

The GPU boundary must be introduced as an adapter immediately before those
semantic calls, not as a replacement router. The forwarder creates
`Simple2dGpuEventBoundaryRequest`; a backend supplies
`Simple2dGpuEventDeviceReceipt`; `Simple2dGpuEventBoundaryPort.decide` is the
only owner selector. CPU ownership invokes the existing dispatch methods;
`none` records stale rejection; GPU ownership will invoke the future bounded
GPU epoch application. This preserves current capture, focus, scroll, key, and
text behavior while an accelerator is unavailable.

## Promotion boundary

Queue state such as queued/submitted/completed-by-host is insufficient. GPU
promotion requires a backend handle plus a device-written receipt correlated by
sequence, scene generation, boundary generation, epoch hash, and commit marker,
then visible production-frame evidence. Until then, the implementation is
boundary infrastructure with CPU execution, not full GPU event offload.
