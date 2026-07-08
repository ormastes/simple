# CPU/GPU Offload Scheduler — Landing Plan

**Status:** Plan for #39. Companion to `doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md`
(blueprint) + `doc/05_design/os/scheduling/cpu_gpu_offload_scheduler_design.md` (OS design).

## Landed (on origin, 2026-07-08)
- **Gap map** (`77e9f385`): unified model over existing infra; HOST-IMPL-NOW vs OS-DESIGN-ONLY split.
- **GPU-offload scheduler design + interpret spec** (`c2882e54`): Gaps #4/#5/#4b, memory_leveling
  integration, pure-logic anchor `test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl`
  (16/0 — rank ordering, placement/backpressure fork, profile-gate + pin lifecycle, sealed-buffer
  protocol).

## Ready to execute — HOST-IMPL-NOW first slice (fully specced, deferred to a fresh session)

**Why deferred:** it touches the bit-exact 2D Metal path and MUST run both `device_readback` gates
with `SIMPLE_SOSIX_GPU_LANE` ON *and* OFF (~10 min of Metal runs) to prove zero pixel change. That
verification needs stable disk + budget; do not ship it unverified.

**The slice (gap map §4; recon confirmed):**
- **File:** `src/lib/gc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl` ONLY (2D lane; leave
  the `nogc_async_mut` twin — it's the browser lane's live import). Currently the evidence-only
  adapter (builds `Engine2dHostGpuDrawIrEventFlowEvidence`, never touches the real FIFO).
- **Flag:** `(env_get("SIMPLE_SOSIX_GPU_LANE") ?? "") == "1"` (default OFF; idiom matches
  `backend_metal.spl:194`).
- **Change when ON:** (a) seal the draw-IR `payload_text` (a seal-marker wrapper: sealed flag +
  payload + hash; one-way seal; post-seal mutation rejected — mirrors `shared_dataset.spl:98,126-133`);
  (b) route the sealed payload through the EXISTING exported primitives
  `engine2d_host_gpu_event_submit_to_runtime_payload_text` (`host_gpu_event_queue.spl:309`) →
  `engine2d_host_gpu_runtime_submit_pending` (`:348`) → `engine2d_host_gpu_runtime_drain` (`:376`);
  (c) treat the drain receipt `ENGINE2D_HOST_GPU_RUNTIME_STATUS_COMPLETED` (=3, `:27`) as the
  completion signal. NO new queue, NO backend_metal op-body change — same bytes ⇒ byte-identical
  Metal dispatch + CPU mirror.
- **Verification (two distinct gate roles — do not conflate):**
  - REGRESSION GUARD (pixels unchanged, flag ON+OFF): `check-engine2d-gpu-offload-evidence.shs`
    (every row MATCH + `source=device_readback`) + `check-engine2d-cpu-metal-parity-evidence.shs`.
  - FUNCTIONAL PROOF (queue path ran): extend `draw_ir_runtime_queue_spec.spl` /
    `host_gpu_event_queue_spec.spl` / `host_gpu_queue_roundtrip_spec.spl` to assert flag-ON
    seal→submit→drain→COMPLETED (not UNAVAILABLE) + seal-rejects-post-seal-mutation.
  - The readback gate does NOT traverse the queue path (its `use` block never imports it) — so it
    proves pixel-safety, the queue specs prove the queue ran. Keep the two claims separate.
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
