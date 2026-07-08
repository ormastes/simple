# CPU/GPU Offload Scheduler — Landing Plan

**Status:** Plan for #39. Companion to `doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md`
(blueprint) + `doc/05_design/os/scheduling/cpu_gpu_offload_scheduler_design.md` (OS design).

## Landed (on origin, 2026-07-08)
- **Gap map** (`77e9f385`): unified model over existing infra; HOST-IMPL-NOW vs OS-DESIGN-ONLY split.
- **GPU-offload scheduler design + interpret spec** (`c2882e54`): Gaps #4/#5/#4b, memory_leveling
  integration, pure-logic anchor `test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl`
  (16/0 — rank ordering, placement/backpressure fork, profile-gate + pin lifecycle, sealed-buffer
  protocol).
- **Gap #1 — SOSIX seal-before-share command buffer** (`693dfd5b`): `SealedDrawIrPayload`
  (build→write→seal→read; one-way seal; post-seal write rejected; djb2 content hash) +
  `engine2d_sosix_gpu_lane_enabled()` flag reader in
  `src/lib/gc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl`; spec
  `sealed_draw_ir_payload_spec.spl` 7/0. Additive — existing consumers unchanged.
- **Gap #2 — SOSIX GPU lane routing (migrate existing GPU offload)** (2026-07-08): flag-gated
  `engine2d_host_gpu_sosix_lane_route(...)` seals the draw-IR payload and routes it through the
  EXISTING runtime GPU queue (emit via `engine2d_host_gpu_event_submit_to_runtime_payload_text` →
  `engine2d_host_gpu_runtime_drain`, COMPLETED=3) to a real receipt; ineligible/host-mutating ops
  fall back to the CPU mirror. Spec `sosix_gpu_lane_route_spec.spl` 3/0 proves seal→route→drained→
  COMPLETED with the payload bytes recovered byte-intact and content-identity re-derived from the
  recovered bytes. No new queue, no backend_metal op-body change. Found + filed a runtime gap along
  the way: `host_gpu_runtime_emit_payload_text_drops_hash_2026-07-08` (text-emit variant does not
  persist the emitted i64 hash; bytes survive → worked around by re-hashing the recovered bytes).

### FUNCTIONAL PROOF done; REGRESSION GUARD (pixel-safety) still to run
The functional half of the HOST-IMPL slice (does the sealed buffer traverse the queue to
COMPLETED?) is LANDED and green. The remaining item is the belt-and-suspenders **pixel-safety**
run: `check-engine2d-gpu-offload-evidence.shs` (every row MATCH + `source=device_readback`) +
`check-engine2d-cpu-metal-parity-evidence.shs`, ideally with `SIMPLE_SOSIX_GPU_LANE` ON and OFF.
Per the gap map, those gates do NOT import the queue path, so they cannot regress from this
additive change (they prove pixels, not the queue) — run when disk headroom allows (~10 min Metal).

- **Correct sequence gotcha (recorded):** the runtime `drain` auto-progresses submit+complete in one
  FFI step (mirrors `draw_ir_runtime_queue.spl:120-128`). Do NOT call `runtime_submit_pending` +
  `runtime_complete_pending` before `runtime_drain` — that leaves the packet in a state the runtime
  drain won't take (`drained=0`). Emit → drain directly.
- **Known pre-existing (not this slice):** `host_gpu_queue_roundtrip_spec.spl` has 2/16 baseline
  failures — stale `Engine2dHostGpuDrawIrEventFlowEvidence.forward`/`.backward` field references
  (the live struct has `event/lane_result/decision/submit/receipt`). Fix or quarantine separately.

## OS-DESIGN-ONLY — boot-blocked dependencies (ship as spec)
- **B1 — freestanding-global fix** (uninitialized module globals / missing module-init in
  freestanding; `freestanding_wrapper_profile_i32_global_var_shifted_2026-07-02`). Blocks running
  ANY OS-side scheduler/compositor under QEMU.
- **B2 — bootstrap stage-2 self-host** (stage-2 empty-MIR; `bootstrap_stage2_empty_mir_bodies_2026-07-05`).
  Blocks OS kernel deploy + Gap #6 self-hosted verification.

### Ordered OS steps (when B1/B2 unblock)
1. **Pure-logic anchor** — DONE (`gpu_offload_sched_class_spec.spl`, no boot needed).
2. **Gap #6 (needs B2):** `Effect::GpuExec` + `Type::GpuComputation<T>` + `@gpu`. Gate: typecheck
   spec + host offload lane routed by the effect. (Design: extend
   `doc/05_design/lib/runtime/execution_context_types_proposal.md`.)
3. **Gap #4 (needs B1):** `park_reason:"gpu_offload"` + backpressure park/re-arm + optional
   `SchedulerPolicy.GpuOffload`. Boot-proof gate: QEMU — a green task parks on `gpu_offload`, a
   completion `smp_send_ipi` wakes it, it drains COMPLETED.
4. **Gap #5 (needs B1 + compositor service task):** SOSIX queue+dataset →
   `compositor_submit_sealed_command_buffer` → Engine2D → `gpu_accel` scanout + completion queue.
   Boot-proof gate: QEMU — userspace submits a sealed command buffer, compositor renders + presents,
   `frame_provenance()` `source=device_readback`, completion queue notifies the client.

## Dependency graph
```
B2 ──► Gap #6
B1 ──► Gap #4 ──► Gap #5   (Gap #5 also needs a compositor service task + 2nd ProcessQueue)
Pure anchor (step 1) — no dependency, DONE.
HOST-IMPL slice — no OS dependency; needs stable disk + budget for the 2-gate verification.
```

## Non-goals (inherited)
No new scheduler, no new IPC stack, no numbered-module split, no rewiring of the gui/web/3d lanes.
The bit-exact CPU mirror invariant must not regress. GPU-tier/placement policy is owned by
`memory_leveling`, not duplicated here.
