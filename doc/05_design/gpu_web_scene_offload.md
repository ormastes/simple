# GPU Web Scene Offload Detail Design

`Simple2dGpuEventBoundaryRequest` is owned by the forwarder and carries input
sequence, event/current scene generations, boundary generation, expected epoch
hash/marker, eligibility, availability, and timeout state.
`Simple2dGpuEventDeviceReceipt` is owned by the backend and carries
completion/device-loss plus matching correlation fields.
`Simple2dGpuEventBoundaryPort.decide` (implemented by the pure decision helper
today) returns exactly one owner (`none`, `gpu`, or `cpu`) plus a stable reason.
`Simple2dGpuEventExecutorPort.execute` is backend-owned and must return
`completed=false` until it has a device-written result buffer and a completed
fence/timeline/readback; queue telemetry is invalid evidence.

Decision order is fail-closed: reject stale input; choose CPU for unsupported or
unavailable work; choose CPU for timeout/device loss/incomplete receipt; verify
sequence, scene, boundary, hash, and nonzero exact marker; only then choose GPU.
A stale input chooses no owner because replay against a newer scene is unsafe.

The future backend adapter must write the receipt after its final mutation
pass. Vulkan flushes non-coherent host writes and waits on a fence/timeline;
WebGPU uploads through queue/staging and maps a readback buffer. Late receipts
are ignored after CPU ownership is committed.

No event-handler objects, host pointers, strings, atlas state, or platform
handles enter Draw IR. Web/GUI/WM integration consumes committed semantic state
through existing scene owners. The first integration adapter wraps the existing
hosted `HostCompositor.dispatch_gui_*` calls; it must not introduce a second
router or change focus/capture policy.
