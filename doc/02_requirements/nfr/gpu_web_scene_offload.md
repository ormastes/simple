# GPU Web Scene Offload NFR

- **NFR-001 Determinism:** identical packets and generations produce identical
  route, mutation order, epoch hash, and owner decision.
- **NFR-002 Safety:** fixed capacity, no host pointers, fail-closed validation,
  no transition-event coalescing, and one commit owner.
- **NFR-003 Portability:** Vulkan, WebGPU, Metal, and CPU oracle implement the
  same packet and receipt semantics despite different memory transport.
- **NFR-004 Performance:** steady-state Simple2D target remains at least 39 FPS;
  event batching is per epoch, not per widget. Promotion needs measured p50/p95
  event-to-present and CPU-time evidence.
- **NFR-005 Observability:** every fallback/rejection exposes a stable numeric
  reason and cold-path text; submission telemetry is never completion evidence.

