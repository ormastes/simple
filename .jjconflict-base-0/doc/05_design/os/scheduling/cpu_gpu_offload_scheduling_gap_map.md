# Unified CPU/GPU Offload Scheduling — Gap Map

**Status:** Design (2026-07-08). Doc-only. No code changed by this document.
**Scope discriminator (hard rule):** for every proposed piece, the single question is
*"does it already live in the scheduler dir, in SOSIX, or in the gpu-flow files?"* If yes →
**reuse it, design only the minimal missing bridge.** This document proposes **no** new
scheduler, **no** new IPC stack, and **no** numbered-module split. It maps the gap over what
exists.

**Two-lane scope split:**
- **[HOST-IMPL-NOW]** — host-side engine offloading (interpret + Metal `device_readback`) is the
  actually-testable target this session.
- **[OS-DESIGN-ONLY]** — the SimpleOS kernel side is design + interpret-mode spec only.
  Freestanding boot (B1/B2) and bootstrap stage-2 are blocked this session, so no QEMU/boot proof
  is possible. The OS side ships as spec.

**Bit-exact invariant (must not regress):** CPU↔Metal parity is proven bit-exact across every
kernel via `device_readback` (`cpu_checksum == metal_checksum`), gated by
`scripts/check/check-engine2d-gpu-offload-evidence.shs` and
`check-engine2d-cpu-metal-parity-evidence.shs`, zero DIVERGE on a 3× reproduction
(`doc/03_plan/ui/rendering/cpu_gpu_dual_algorithm_plan.md` STATUS ROLL-UP). Any new
scheduling/queue layer routes **behind a flag, on ONE lane** (the 2D Engine2D Metal path already
on `host_gpu_draw_ir_event_flow`), keeps those gates green, and does **not** rewire all four
(gui/web/2d/3d) lanes.

---

## 1. EXISTS — what is already built (one row per subsystem)

| Subsystem | Already built (file:line) | Role in a CPU/GPU offload model |
|---|---|---|
| **CPU scheduler** | `Scheduler` = `_Scheduler` package re-export (`src/os/kernel/scheduler/scheduler.spl:13-16`); green layer: `GreenTaskRecord` (`green_task.spl:17-25`), pure placement fns `green_worker_pick_spawn_cpu`/`_choose_wake_cpu`/`_rebalance_decision`/`_should_steal` (`green_worker.spl`), carrier bridge `GreenCarrier*` enqueue+`smp_send_ipi` wake (`green_carrier.spl:20,360-384,897-937`) applied via `Scheduler.apply_green_scheduler_intent` (`_Scheduler/scheduler_lifecycle.spl:542`). Classes: `SchedulerPolicy` (`task_types.spl:49-57`), rank `sched_class_rank` (`scheduler_algorithm.spl:26-35`). | The **CPU green-thread scheduler**. Carrier = fixed per-CPU execution slot; worker = pure placement policy; task = schedulable unit. This is the lane that would *emit* GPU-offload work and *await* its completion. Ground truth. (`sched_policy_engine.spl`/`sched_class_queue.spl` are **orphan/unwired** — zero external refs — do NOT build on them.) |
| **SOSIX IPC** | Syscall-routed pair: `shared_dataset.spl` + `process_queue.spl`, exposed as syscalls 120-131 (`ipc/syscall.spl:687-734` → `_handle_dataset_*`/`_handle_queue_*`, `syscall_spm.spl:330-417`), cap-gated (`CapabilityKind.SharedDataset`/`ProcessQueue`). Seal-before-share enforced at the write gate (`shared_dataset.spl:98`); one-way `seal` (`:126-133`); `read` rejects-unless-sealed (`:160`); ABA-safe `generation<<16|slot` handle, `close` bumps generation (`:151`); zero-copy `dataset_map`→`vmm_mmap` (`syscall_spm.spl:367-373`). Bounded queue `send(bytes, attached_dataset)` requires attached dataset already sealed (`process_queue.spl` send gate). | The **communication substrate**: sealed-dataset = immutable **command buffer**, bounded queue = **dispatch channel**, queue notify = **completion signal**. The in-process twin `os/sosix/share.spl` is **dormant** (zero production callers except one unused wrapper) — the syscall pair is the substrate a real CPU→GPU channel rides. Caps: 64 datasets, 4096 B each — a full draw-IR list needs chunking or a bigger arena. |
| **Host GPU flow** | Real bounded FIFO: `host_gpu_event_queue.spl:137-229` (runtime-backed, `Mutex<HostGpuQueueState>` + 2×`VecDeque`, cap 1024, `host_gpu_lane.rs:55-91`) with `emit→QUEUED→submit→SUBMITTED/in-flight→complete→COMPLETED/UNAVAILABLE→drain`; pure-Simple twin `Engine2dHostGpuPureQueueState` (`:115-301`). Draw-IR tie-in `host_gpu_draw_ir_event_flow.spl:34-41` (policy adapter, **evidence-only** path). Runtime-wired path `draw_ir_runtime_queue.spl` `engine2d_draw_ir_runtime_queue_dispatch` (`:101-141`), called from `draw_ir_adv.spl:329`, `ui.browser/backend.spl`, `web_render_pixel_backend.spl:86-109`. Session metadata: `backend_session.spl` (`backend_session_create` mints handle only, `:157-171`). | The **host GPU-offload lane**: an already-real bounded dispatch queue with a typed completion receipt. But it is **synchronous, same-thread, polled by the caller** — no background worker, no fence/callback; "in flight" = popped from one VecDeque into another. This is a *parallel* queue to SOSIX, not built on it. |
| **Dual-algorithm decision** | Capability fork `BackendCapability{kind,device_present,accelerated_ops}` `is_accelerated(op)` (`backend_capability.spl:38-56`), each backend self-reports live pipeline handles (`backend_metal.spl:590-618`). Live dispatch self-gates per-op on the raw pipeline field (`indexed_fill()` `backend_metal.spl:625-655`: unconditional CPU mirror first, then `if pipe_*==0: fallback`, then one synchronous Metal dispatch). Host eligibility `engine2d_host_gpu_lane_schedule` (`backend_lane.spl:175-193`, packet-size/no-host-mutation/batch-op check). | The **placement fork** ("does this op go GPU?"). It is a **static, synchronous, one-op-at-a-time gate**, not a scheduler. `is_accelerated()` is the gate-side verification read (`engine2d_gpu_offload_evidence.spl:340`); `pipe_*==0` is the dispatch-side read — *two evaluations of one fact*. `Engine2D` facade branches on **which backend** was picked at construction, never per-op. |
| **Exec-context** | Design draft only: `execution_context_types_proposal.md` (`@gpu(device)`/`@host(cpu)`, `Type::GpuComputation`/`HostComputation`, `Effect::GpuExec`/`HostExec`, `ExecutionContext{Host/Gpu/Auto}`) — **Status: Draft, unstarted** (grep: zero matches in `src/`). Live `Effect` enum still only `Sync`/`Async` (`effects.rs:37-42`, `effects.spl:18-21`). OS GPU driver `gpu_accel.spl`: **presentation-only** (`present_full`/`present_dirty`→virtio-gpu flush, header line 4-6 "GPU acceleration is for present() only"), no compute queue/kernel/device-select. Compositor `compositor_engine2d.spl` wraps one `Engine2dCompositorBackend`. | The **type-level placement axis** the model would eventually be typed by, and the **OS-side device/queue surface**. Both are gaps: no device-execution-context type exists, and the OS GPU driver has no compute-dispatch surface (scanout only). |
| **Memory placement** | No dedicated doc (confirmed by find/grep). Reconstructed from code: `MetalBackend` holds `mirror: SoftwareBackend` (CPU oracle) + `d_framebuffer` (persistent device buffer, alloc once `backend_metal.spl:371`). Every op dual-writes mirror then best-effort GPU. Bulk data uses **per-call host-staging** `rt_alloc`→`metal_buffer_upload_ptr`→fresh `metal_sffi_alloc_buffer`, **freed immediately, no pooling** (`:709-788`,`:845-887`). Unified memory: `StorageModeShared` + `contents()` memcpy (`metal_graphics_runtime.rs:329-365`). Persistent-resident exceptions: LUT (re-upload on `(version,count)` change, `:657-684`) and glyph atlas (once at init, `:692-707`). | The **command-buffer / staging model**. The sealed-dataset "command buffer" concept maps onto the draw-IR payload; the per-call alloc/free is the staging today. Not itself a scheduling gap — a downstream optimization (pooling) noted for completeness. |

---

## 2. THE UNIFIED MODEL (conceptual — how the existing pieces compose)

The model is a single sentence assembled entirely from parts that already exist:

> **A CPU green-thread scheduler** (`GreenCarrier` per-CPU slots + `green_worker` placement)
> **emits GPU-offload work to a GPU-offload lane**, communicating via **SOSIX
> sealed-dataset (the command buffer)** + **bounded-queue (the dispatch channel)** +
> **completion-signal (queue notify / drain receipt)**, and **decides placement via the
> dual-algorithm capability fork** (`is_accelerated` / `pipe_*==0` / `lane_schedule` eligibility).

Composition, piece by piece — nothing new, only wiring:

```
  CPU lane (exists)                 communication (exists)              GPU lane (exists)
  ┌───────────────────┐            ┌───────────────────────┐          ┌────────────────────┐
  │ GreenCarrier slot  │  place?   │ SEAL draw-IR payload   │  submit  │ Metal dispatch     │
  │ green_worker pick  │──fork────▶│ = sealed-dataset       │─────────▶│ (pipe_*, sync)     │
  │ (dual-algo:        │           │ (command buffer)       │          │ backend_metal      │
  │  is_accelerated /  │           │ ↓ enqueue on           │          │ + CPU mirror oracle│
  │  lane_schedule)    │           │ bounded-queue (dispatch)│          └─────────┬──────────┘
  │                    │◀──────────│ ← completion-signal ────│◀───drain/receipt───┘
  └───────────────────┘  await     │ (queue notify / receipt)│  COMPLETED / UNAVAILABLE
                                    └───────────────────────┘
```

1. **Placement (the fork).** When the green scheduler has drawing work, the existing dual-algo
   fork decides CPU-vs-GPU: `engine2d_host_gpu_lane_schedule` eligibility + `is_accelerated(op)`.
   GPU-eligible work becomes an offload packet; everything else stays on the CPU mirror. No new
   decision logic — the fork already exists, one op at a time.
2. **Command buffer = sealed dataset.** The draw-IR payload becomes an **immutable** command
   buffer by adopting SOSIX's *seal-before-share* invariant: seal the payload, then it is
   read-only for the consumer. This is exactly `SharedDataset.seal` semantics; today the host
   payload is raw un-sealed `payload_text`.
3. **Dispatch = bounded queue.** The sealed command buffer is enqueued on a bounded queue. On the
   **host lane this is the already-real `host_gpu_event_queue`** (cap 1024); on the **OS lane this
   is `ProcessQueue`** (syscalls 120-131) with the sealed dataset as its `attached_dataset`
   (which the send gate already requires to be sealed). Same shape, two substrates.
4. **Completion signal.** The consumer signals done via the existing typed receipt
   (`Engine2dHostGpu*ReceiptEvidence` / `runtime_drain` → `COMPLETED`/`UNAVAILABLE`) on the host,
   or SOSIX queue notify on the OS side. The green scheduler's awaiting carrier is woken (the
   `smp_send_ipi` / carrier-intent path already exists).

The bit-exact CPU mirror stays exactly where it is: it is written **unconditionally, first**, on
every op. The scheduling layer sits *around* dispatch, never *inside* the pixel path — which is
why routing behind a flag cannot change a single pixel.

---

## 3. GAP LIST — the minimal missing bridges only (ranked)

Each gap is a *bridge between two things that already exist*, not a new component. Tagged and
ranked by "smallest testable proof first".

### [HOST-IMPL-NOW] — testable this session (interpret + Metal device_readback)

1. **Seal-before-enqueue on the host draw-IR payload.** *(rank 1 — the first slice)*
   Bridge: adopt SOSIX `SharedDataset.seal` immutability semantics on the payload before it enters
   `host_gpu_event_queue`. **Touches:** `draw_ir_runtime_queue.spl` (`:101-141`) +
   `host_gpu_event_queue.spl` (`:309-327` runtime submit path). **Why not already there:** the host
   queue emits raw `payload_text` with no seal/immutability gate; SOSIX's seal-before-share
   invariant lives only in `shared_dataset.spl`, which the host lane never calls.

2. **Route `host_gpu_draw_ir_event_flow` through the runtime queue behind a flag.**
   Bridge: the policy adapter uses the **evidence-only** path today (never touches the FIFO,
   `host_gpu_draw_ir_event_flow.spl:34-41`); its runtime-wired twin `draw_ir_runtime_queue.spl`
   exists but is only reached from `draw_ir_adv`/`ui.browser`/`web_render_pixel_backend`. **Touches:**
   `host_gpu_draw_ir_event_flow.spl`. **Why not already there:** the two paths were built as
   parallel siblings; nothing wires the certification-evidence flow to the real FIFO under a gate.

3. **Single shared placement call (fold the two-evaluations-of-one-fact).** *(rank low)*
   Bridge: `is_accelerated(op)` (gate-side) and `pipe_*==0` (dispatch-side) evaluate the same fact
   independently; `lane_schedule` is a third. **Touches:** `backend_capability.spl` +
   `backend_lane.spl` + `host_gpu_draw_ir_event_flow.spl`. **Why not already there:** honest
   self-description was built per-backend; no shared decision seam. *Optional* — only pursue if it
   removes divergence risk; do **not** over-engineer a router the facade doesn't need.

### [OS-DESIGN-ONLY] — design + interpret-mode spec, boot-blocked (ships as spec)

4. **GPU-offload as a first-class lane in the green scheduler.**
   Bridge: add a GPU-offload sched class so dispatch is a *schedulable, awaitable* lane instead of
   an out-of-band synchronous poll. **Touches (spec):** `scheduler_types.spl` /
   `task_types.spl:49-57` (`SchedulerPolicy`) + `green_carrier.spl`. **Why not already there:** the
   green scheduler models CPU slots only; a GPU carrier slot / offload-wait state does not exist.
   Design only — cannot boot-prove this session.

5. **Wire SOSIX kernel queue+dataset to the OS GPU driver / compositor.**
   Bridge: a userspace client submits a sealed command buffer (`shared_dataset` syscall 124 `map`)
   + bounded dispatch (`process_queue` send with sealed `attached_dataset`) to the compositor.
   **Touches (spec):** `gpu_accel.spl` + `compositor_engine2d.spl` + `syscall_spm.spl:330-417`.
   **Why not already there:** `gpu_accel.spl` is presentation-only (no compute queue); SOSIX
   syscalls exist but have zero production callers on the GPU path. Design only — boot-blocked.

6. **Device execution-context type for placement.**
   Bridge: the model's runtime fork would eventually be typed by `Type::GpuComputation` /
   `Effect::GpuExec` (`@gpu(device)`), letting the compiler track *where* an op runs. **Touches
   (spec):** `execution_context_types_proposal.md` + `effects.spl:18-21` / `effects.rs:37-42`.
   **Why not already there:** the proposal is an unstarted Draft; live `Effect` is `Sync`/`Async`
   only. Design only — orthogonal to the testable slices; do not block on it.

7. **Staging-buffer pooling (adjacent, not scheduling).** *(note only)*
   Per-call `rt_alloc`/free with no pooling (`backend_metal.spl:709-788`). A pool would ride the
   sealed-dataset command-buffer lifecycle. Recorded so it is not lost; **not** part of the
   scheduling bridge and not required by any slice.

---

## 4. FIRST TESTABLE SLICE — smallest host-side change that proves the model

**One flag, one lane, zero pixel change.**

- **Flag:** `SIMPLE_SOSIX_GPU_LANE=1` (default OFF — legacy evidence-only path unchanged when unset).
- **Lane:** the 2D Engine2D Metal path only — the `coarse_batch` GPU branch of
  `host_gpu_draw_ir_event_flow` (already on `host_gpu_draw_ir_event_flow`). Do **not** touch the
  web/gui/3d lanes.
- **Change (Gap #1 + #2 composed):** when the flag is set, `host_gpu_draw_ir_event_flow` (a)
  **seals** the draw-IR payload (SOSIX seal-before-share semantics) into an immutable command
  buffer, then (b) routes it through the **existing** `draw_ir_runtime_queue` →
  `host_gpu_event_queue` submit/drain instead of the evidence-only path, and (c) treats the
  existing `runtime_drain` receipt (`COMPLETED`/`UNAVAILABLE`) as the completion signal. No new
  queue, no new dispatch, no change to any `backend_metal` op body — the sealed buffer carries the
  same bytes, so the Metal dispatch and the CPU mirror are byte-identical to today.
- **Why this proves the model:** it exercises **sealed-dataset (command buffer) + bounded-queue
  (dispatch) + completion-signal** end-to-end on a real lane, using only pieces that already exist,
  with the placement fork unchanged. (On host this *adopts SOSIX seal-before-share semantics* on
  the `payload_text` — it does not call `SharedDataset` proper; SOSIX-proper runs only on the OS
  design-only side.)

**Two gate roles — a regression guard AND a functional proof are both required.**

*Verified 2026-07-08:* `grep` shows neither readback harness references
`host_gpu_draw_ir_event_flow` / `draw_ir_runtime_queue` / `host_gpu_event_queue`. So the readback
gates render via `Engine2D`→`backend_metal` ops directly and do **not** traverse the queue path.
They therefore prove *pixel-safety* (the change didn't break the 2D lane), **not** that the
sealed-dataset+queue+completion path ran. Both roles are needed:

- **Regression guard (pixels unchanged on the 2D lane) — MUST stay green, flag ON and OFF:**
  - `scripts/check/check-engine2d-gpu-offload-evidence.shs` running
    `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl` — `compare_exact` +
    `source == device_readback` (a `cpu_mirror` source = silent software fallback = HARD FAIL) for
    **every** row: `wm_composite`, `primitives`, `text`, `text_edge`, `indexed_fill`,
    `gradient_rect`, `rounded_rect`, `image`.
  - `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` running
    `engine2d_cpu_metal_parity_run.spl` — pixel-exact CPU↔Metal, `gpu_ok=true` on macOS (skip is
    **not** a pass).
- **Functional proof (the queue path actually ran) — MUST assert seal→submit→drain→COMPLETED:**
  the slice's own behavior is proven by the **existing** queue specs, extended to assert the flag
  path: `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl` (+ its
  `nogc_async_mut` twin), `.../host_gpu_event_queue_spec.spl`, and the integration round-trip
  `test/02_integration/lib/gpu/host_gpu_queue_roundtrip_spec.spl`. These assert the sealed payload
  is enqueued, drained, and completes `COMPLETED` (not `UNAVAILABLE`) — the part the readback gates
  cannot see.

**Lane-identity note.** `draw_ir_runtime_queue`'s *current* live callers are the web/browser lane
(`ui.browser/backend`, `web_render_pixel_backend`), while the readback gates are the **2D Engine2D**
lane. The slice joins them at `host_gpu_draw_ir_event_flow` (the 2D policy adapter): under the flag,
the 2D lane routes through the runtime queue. If that join is not reachable by the readback harness
(it is not today), the split is explicit — the **readback gates guard 2D pixel-safety**, the
**queue specs prove the sealed-dataset+queue+completion path**. Do not claim the readback gate
proves the queue ran.

**Pass condition:** regression gates green with the flag ON (no pixel perturbation) *and* OFF (no
legacy regression), zero DIVERGE on the 3× reproduction; **and** the functional queue specs green
asserting the flag-on seal→submit→drain→COMPLETED path.

---

## 5. DEPLOYABLE-NOW vs DESIGN-ONLY — summary

| Piece | Tag | Ships as |
|---|---|---|
| Gap #1 seal-before-enqueue (host 2D lane) | [HOST-IMPL-NOW] | **Deployable** — the first testable slice, behind `SIMPLE_SOSIX_GPU_LANE=1` |
| Gap #2 route evidence-flow → runtime queue | [HOST-IMPL-NOW] | **Deployable** — composed into the first slice |
| Gap #3 shared placement call | [HOST-IMPL-NOW] (optional) | Deployable if pursued; skip unless it removes divergence risk |
| Gap #4 GPU-offload sched-class in green scheduler | [OS-DESIGN-ONLY] | **Spec** — boot-blocked (B1/B2 + stage-2) |
| Gap #5 SOSIX queue+dataset → OS GPU driver/compositor | [OS-DESIGN-ONLY] | **Spec** — boot-blocked |
| Gap #6 device exec-context type (`@gpu`/`GpuExec`) | [OS-DESIGN-ONLY] | **Spec** — unstarted proposal |
| Gap #7 staging pool | note only | Backlog note (not scheduling) |

**Bottom line:** the host 2D lane ships a real, flag-gated proof of the unified model this session
(Gaps #1–#2), keeping the two `device_readback` gates green. The **entire SimpleOS kernel side
(Gaps #4–#6) ships as spec** — it is designed against existing files (`green_carrier`,
`process_queue`/`shared_dataset` syscalls, `gpu_accel`, `effects`) but cannot be boot-proven while
freestanding boot and bootstrap stage-2 are blocked.
