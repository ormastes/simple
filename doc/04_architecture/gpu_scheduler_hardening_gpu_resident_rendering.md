<!-- codex-architecture -->
# GPU Scheduler Hardening and GPU-Resident Rendering Architecture

## Status

Proposed architecture; the first implementation increment is deferred DrawIR
completion over the existing host-GPU queue.

## Ownership and boundaries

`Engine2dHostGpuRuntimeQueue` is the sole mutable native-queue owner. The
producer freezes a DrawIR payload summary/registered payload descriptor and
commits one bounded request. The provider alone advances it through submitted,
completed, drained, and retired states. Callers receive copied receipts, not
native handles or mutable queue access.

```text
DrawIrComposition -> packed/registered payload -> bounded runtime queue
                                              -> provider submit
                                              -> provider completion ingress
                                              -> owner drain/retirement
                                              -> Engine2D backend/present service
```

The existing SDN payload is compatibility-only. A future packed payload is a
DrawIR v3 encoding of existing display-list semantics, not a competing WebIR.

## Deferred operation contract

`engine2d_draw_ir_runtime_queue_submit_deferred` submits only. Its receipt
identifies queue/backend/payload provenance and returns pending state. Existing
`engine2d_host_gpu_runtime_complete_pending` advances the current compatibility
provider phase; its foreign operation currently has no queue/generation token,
so it is routing evidence only and cannot prove queue-specific native GPU
completion. The legacy dispatch function retains immediate drain behavior for
existing callers until they migrate.

## Resident-scene profile boundary

The strict profile allows host bootstrap, platform-thread-affine input,
submission, and presentation. It forbids CPU event/style/layout/DrawIR/raster
fallback for admitted work. This is a capability policy over existing
Engine2D/Object-VM/SOSIX contracts, not a new scheduler or browser tree.

## Safety invariants

- Bounded reservation includes request and completion capacity.
- Generation, backend, surface, and payload provenance are validated before
  dispatch and retirement.
- Completion and retirement are distinct; cancellation never frees in-flight
  storage early.
- Unknown cross-domain access is treated as overlapping; no raw pointers cross
  the safe boundary.
- Queue full, malformed payload, stale generation, resize, and device loss
  return explicit failure/blocked receipts.

## Follow-up common contract

Create `Engine2dGpuEpochRequest`/`Engine2dGpuEpochReceipt` only in
`src/lib/common/gpu/engine2d/`, composed from existing SimpleRing metadata,
leases, tokens and completions. It must keep queue, operation, scene, surface,
and arena generations separate. Map profiles onto existing DrawIR v3 execution
route and GPU-web receipt contracts rather than creating another hierarchy.

`common/mission_critical/draw_ir_packed_generation_store_v3.spl` is reusable
for bounded generation handoff, but its current hash formats all rows into
growing text. It is not proof of a static-pool hot path until sealing uses
binary incremental hashing or a startup-only digest.

## Next architecture paths

`src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl`,
`src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl`,
`src/lib/nogc_async_mut/async_ring/simple_ring.spl`, and
`src/lib/common/contracts/execution/simple_ring_async_v1.spl`.
