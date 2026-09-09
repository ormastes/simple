# Rendering and UI Feature Group

Base knowledge for GPU offload, Engine2D, web rendering, compositor drawing,
fonts, input routing, RenderDoc, and UI evidence. Generated artifacts never
substitute for native device-origin evidence.

## GPU-resident UI optimization contract

- A renderer cache proves reuse only when surface resize, device loss, shutdown,
  and memory accounting have deterministic owners. Process-lifetime caches are
  not a completed residency design.
- Production display must use device-present without framebuffer readback.
  Readback is reserved for explicit capture/parity runs and stays outside the
  timed steady-state interval.
- Async claims require backend submission identities, real fence/timeline
  completion, nonblocking poll/retire, and bounded frames in flight. Enqueue
  followed by immediate drain proves routing, not asynchronous GPU execution.
- Event work should produce bounded semantic deltas and damage generations;
  it must not force full-scene serialization, full-buffer upload, or immediate
  CPU/GPU synchronization per event.
- C Vulkan, Simple Vulkan, and Chrome comparisons must use the same scene,
  viewport, sample policy, timing boundary, readback mode, and device/fallback
  admission. Retain p50/p95, RSS, revision/binary identity, and checksum proof.
- Calculate the selected Vulkan comparison as `Simple p95 / C p95` with a 2.0x
  ceiling. Do not substitute FPS direction or a legacy 10% floor.
- A benchmark row is publishable only after common receipt admission. Raw
  `measured-unadmitted`, synthetic, fixture-only, CPU-fallback, unknown (`-1`),
  or bootstrap-seed rows produce no ratio.
- Require zero timed buffer allocations/full-frame uploads/framebuffer
  readbacks, retained bytes with teardown release, completion polls, bounded
  damage, and event/frame generations. Keep one exact RGBA8 capture outside
  timing and require its full byte count.
- For native renderer or Chromium bridge calls, never reinterpret ordinary
  boxed Simple arrays as stable pointers. Use scoped pinned byte-span calls for
  inputs and packed runtime byte arrays for mutable outputs.

## Residency, queue, and event scheduling rules

- Treat a surface as GPU-resident only while its device allocation is owned by
  the surface capsule and its byte count is observable. Persistent mapped
  memory is an upload mechanism, not proof that the framebuffer is resident:
  keep device-local render targets resident and use a bounded, persistently
  mapped staging ring for host writes. Avoid map/unmap and allocation in the
  timed frame path; report `allocation_count`, `retained_bytes`,
  `staging_bytes`, and `upload_bytes` separately, and require all four to have
  a teardown receipt.
- A staged upload must have an explicit ownership handoff: write mapped
  staging bytes, flush only the non-coherent range when required, record the
  transfer, then release/acquire into the graphics queue (or document one
  queue as the owner). Record queue-family/queue identity and the barrier or
  timeline value. A host-visible buffer or completed queue packet alone does
  not establish device execution.
- Input events are host-owned and should coalesce into a bounded damage set
  tagged with a scene generation. Schedule one frame for the next available
  slot; do not submit-and-wait or drain the GPU from every event. Freeze the
  damage before recording, and retire a slot only after its matching fence or
  monotonic timeline value is observed by nonblocking poll. Stale generations
  are discarded, not synchronized into an in-flight frame.
- C Vulkan and Simple Vulkan must share fixture/event hashes, viewport, RGBA
  format, warmups, samples, timing boundaries, ring depth, queue/device
  identity, and capture policy. Simple Web and Chrome additionally require
  the same semantic primitive/event trace and a declared device-origin
  receipt. If the canonical Chrome library/runner is absent, source fixtures,
  Electron DOM evidence, or a diagnostic dylib remain **non-admitted** and no
  web ratio is published.
