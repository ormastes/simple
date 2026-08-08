# GPU Web Scene Offload Requirements

Selected by the user on 2026-08-02: GPU-first bounded event management with
explicit CPU fallback, projected through Simple2D → Web → GUI → WM.

- **REQ-001:** OS or optional IO input shall be normalized by a thin CPU
  forwarder into ordered, versioned, bounded packets without owning widget
  semantics.
- **REQ-002:** A GPU result shall own an event commit only when a device-written
  completion receipt matches event sequence, scene generation, boundary
  generation, epoch hash, and a nonzero submission commit marker.
- **REQ-003:** Unsupported, unavailable, timeout, device-loss, overflow, or
  invalid-receipt cases shall select the CPU oracle with a named reason and
  shall never allow both CPU and GPU to commit. Stale-scene input is rejected,
  not replayed.
- **REQ-004:** GPU-owned state shall project through canonical Simple2D/Draw IR,
  then Web, GUI, and WM owners. Privileged host effects remain CPU services.
- **REQ-005:** Full WM GPU ownership is a target, not a current claim. Promotion
  requires a real backend kernel, device receipt/readback, production frame
  integration, and independent visible evidence.

