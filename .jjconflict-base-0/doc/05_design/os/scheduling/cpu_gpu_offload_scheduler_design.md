# GPU-Offload Scheduler Design (SimpleOS side) — Gaps #4 & #5

**Status:** [OS-DESIGN-ONLY] Design + interpret-mode spec. Boot-blocked (freestanding
B1/B2 + bootstrap stage-2) → ships as SPEC. No production code changed by this document.
**Companion:** `doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md`
(the blueprint; §1 EXISTS, §2 MODEL, §3 Gaps, §5 summary).
**Scope rule (inherited):** design ONLY the minimal missing bridge over what exists in the
scheduler dir + SOSIX + gpu-flow files + the peer `memory_leveling` capsule. No new
scheduler, no new IPC stack, no numbered-module split.

**HOST-IMPL-NOW vs OS-DESIGN-ONLY:** the host 2D lane (Gaps #1–#2, `SIMPLE_SOSIX_GPU_LANE=1`)
is the separately-testable anchor. Everything below is the SimpleOS kernel half — designed
against existing files but not boot-provable this session.

> **Path correction to the gap map:** `SchedulerPolicy` is at
> `src/os/kernel/types/task_types.spl:49-57` (not `.../scheduler/task_types.spl`); confirmed
> by the import at `src/os/kernel/scheduler/scheduler_algorithm.spl:6-9`.

---

## Gap #4 — GPU-offload as a schedulable, awaitable lane

### Ground truth (files this designs against)
- `SchedulerPolicy` enum — `src/os/kernel/types/task_types.spl:49-57`
- `BlockReason` enum (Notification variant) — `src/os/kernel/types/task_types.spl:31-39`
- `sched_class_rank` — `src/os/kernel/scheduler/scheduler_algorithm.spl:26-35`
- `sched_wakeup_preemption_decision` (rank consumer) — `.../scheduler_algorithm.spl:41-89`
- `GreenTaskRecord{state,park_reason}` — `src/os/kernel/scheduler/green_task.spl:17-25`
- `green_task_park / _unpark / _complete` — `.../green_task.spl:55-65 / 67-96 / 98-113`
- carrier wake `green_carrier_apply_enqueue` → `smp_send_ipi` — `.../green_carrier.spl:897-937`
  (IPI at `:920`; const `GREEN_CARRIER_RESCHEDULE_IPI` `:20`; import `:18`)
- `green_carrier_enqueue_task` — `.../green_carrier.spl:939`

### Key insight — the awaitable lane already exists
`GreenTaskRecord` carries `state: text` (`runnable/parked/done`) and free-form
`park_reason: text` (`green_task.spl:22-24`). GPU offload is modeled as a **park with reason
`"gpu_offload"`**, requiring NO new scheduler primitive.

### Design (where each hook goes)
1. **Emit an offload packet + await.** The green task calls
   `green_task_park(task, reason:"gpu_offload")` (`green_task.spl:55`). Parked ⇒ consumes no
   CPU; the emitting worker slot is freed. (Kernel TCB side: block with
   `BlockReason.Notification(id: completion_token)` — reuse `task_types.spl:39`; no new type.)
2. **Completion wake path (existing, unchanged).** On completion, call
   `green_task_unpark(task, waker_cpu, …)` (`green_task.spl:67`) → `GreenTaskWakeDecision` →
   `green_carrier_enqueue_task` (`green_carrier.spl:939`) → `green_carrier_apply_enqueue`
   (`green_carrier.spl:897`) → `smp_send_ipi(target_cpu, GREEN_CARRIER_RESCHEDULE_IPI)`
   (`green_carrier.spl:920`). Same remote-wake path as every other unpark.
3. **Backpressure (bounded queue full).** The dispatch queue returns `EAGAIN` when
   `count >= capacity` (`process_queue.spl:151-152`). Emitting task parks
   `reason:"gpu_offload_backpressure"`, re-arms on `POLL_WRITE` readiness
   (`process_queue.spl:210`); degradation = fall back to the unconditional CPU mirror (never a
   hang). No new queue — the bound is the existing `ProcessQueue` capacity.
4. **Optional sched CLASS + RANK (additive refinement).** Append `GpuOffload` to
   `enum SchedulerPolicy` (`task_types.spl:49-57`) and `case GpuOffload: 3` to `sched_class_rank`
   (`scheduler_algorithm.spl:26-35`) — Fair tier, **no existing rank renumbered**. Completion-wakes
   never preempt RT/Deadline (rank 3 > 2/1), never starve (3 < 5 Idle). Optional because the wait
   is off-CPU; by default the woken task re-enters at its original class.

**Not added:** no background dispatch thread, no new run-queue, no new IPI kind, no per-op
scheduler. The scheduling layer sits around dispatch, never inside the pixel path.

---

## Gap #5 — SOSIX queue+dataset → OS GPU driver / compositor

### Ground truth
- `shared_dataset.spl`: seal-before-share write gate `:98`; one-way `seal` `:126-133`;
  read-rejects-unless-sealed `:160`; ABA handle `generation<<16|slot` `:43-44`;
  `shared_dataset_is_sealed` `:200-204`. Caps: 64 datasets × 4096 B `:9-10`.
- `process_queue.spl`: `send(bytes,attached) :142-167` (EAGAIN-when-full `:151-152`);
  `recv :169-199`; `poll :201-214` (`POLL_READ :208-209`, `POLL_WRITE :210`).
- `syscall_spm.spl` (120–131): `_handle_dataset_seal :363-365`; `_handle_dataset_map` →
  `vmm_mmap` zero-copy `:367-373`; `_handle_queue_send` (requires attached sealed) `:388-396`;
  `_handle_queue_recv :398-409`; `_handle_queue_poll :411-413`.
- `gpu_accel.spl`: presentation-only — header `:1-6`; `present_full :61-63`; `present_dirty :65-67`.
- `compositor_engine2d.spl`: `Engine2dCompositorBackend` wraps one `Engine2D` `:23-24`;
  ops `:77-101`; `present :103`; `frame_provenance()` `source=device_readback` `:63-65`.

### Design
`gpu_accel.spl` is **scanout-only** and stays that way (VirtIO-GPU 2D has no compute shaders).
The **compute/dispatch submit surface goes on the COMPOSITOR**, which already wraps a real
`Engine2D` that can carry a GPU backend; `gpu_accel` remains the downstream scanout stage.

- **New entrypoint (spec):** `compositor_submit_sealed_command_buffer(cmd_handle:u64,
  dispatch_hdr:[u8]) -> completion_token`. `gpu_accel` gains a design-only sibling
  `gpu_accel_dispatch_sealed(...)` routing to the Engine2D compositor.
- **Client submit (existing syscalls):** `dataset_create`(120) → `dataset_write` →
  `dataset_seal`(122) ⇒ sealed handle = command buffer → `queue_send(queue, hdr,
  attached=sealed_handle)` (gate `syscall_spm.spl:393-395` requires attached sealed).
- **Server (compositor):** blocks on `queue_recv`/`queue_poll`; maps the sealed dataset zero-copy
  (`dataset_map`→`vmm_mmap`), decodes draw-IR, drives `Engine2dCompositorBackend` → `present()` →
  `gpu_accel.present_dirty`; provenance `source=device_readback` (`cpu_mirror` = fail).
- **Completion:** a second `ProcessQueue` (completion channel); server `queue_send`s status; the
  client's parked green task unparks on `queue_recv` readiness — joining Gap #4's wake path.

### Communication protocol (same shape, two substrates — gap map §2)
| Role | Host [HOST-IMPL-NOW] | OS [OS-DESIGN-ONLY] |
|---|---|---|
| Command buffer | sealed `payload_text` | `SharedDataset` sealed handle |
| Dispatch | `host_gpu_event_queue` (cap 1024) | `ProcessQueue` send + sealed attach |
| Completion | `runtime_drain` COMPLETED/UNAVAILABLE | 2nd `ProcessQueue` notify → `green_task_unpark` |

**Constraint:** 4096-byte dataset cap (`shared_dataset.spl:10`) ⇒ a full draw-IR list must be
chunked across datasets or use a larger arena; recorded, not designed here.

---

## Gap #4b — Integration with the peer `memory_leveling` capsule (2026-07-08)

A parallel peer workstream landed `memory_leveling` on origin *after* the gap map. The GPU
scheduler must **consume** its placement intent, not duplicate it — memory placement is exactly
where CPU/GPU scheduling meets the memory hierarchy.

### Ground truth (peer files, on origin)
- `src/lib/nogc_sync_mut/memory_leveling.spl` (platform-neutral placement intent; `T`/`mut T`/
  `iso T`/device-handle ownership as pure intent).
- `src/os/kernel/memory/memory_leveling.spl` (pure policy capsule — profiles, page states,
  decisions `keep`/`swap_out`/`promote_cpu`/`demote_cold`/`pin_device`/`reject`).
- `test/03_system/os/simpleos_memory_leveling_spec.spl`; arch/design
  `doc/04_architecture/simpleos_memory_leveling.md`, `doc/05_design/simpleos_memory_leveling.md`.

### The integration contract (scheduler consumes, does not duplicate)
1. **A sealed command buffer's backing page is a `pin_device` candidate.** When the scheduler
   seals a draw-IR dataset (Gap #5) and hands its page to the compositor for zero-copy
   `dataset_map`, that page is being read by the device → it must be `pin_device` so the VMM does
   not swap/demote mid-dispatch. This is the capsule's rule *"GPU-resident pages reject swap and
   demotion until a coherence proof exists"* (`doc/04_architecture/simpleos_memory_leveling.md:40`).
   The scheduler requests `pin_device` on submit, releases on completion.
2. **`heterogeneous_device` is the GPU-scheduling profile.** The capsule's three profiles gate GPU
   tiering: `baremetal_static` (no GPU tier), `simpleos_default` (CPU pages only),
   `heterogeneous_device` (GPU tier + DMA pin + shadow copies). The GPU-offload sched class is
   active only under `heterogeneous_device`; the other two always yield `cpu_mirror` — one shared
   gate, no duplicated tiering logic.
3. **Coherence proof = the completion signal.** The capsule pins a GPU-resident page "until a
   coherence proof exists." The scheduler's completion token (Gap #5 notify / host `runtime_drain`
   receipt) IS that proof: on `COMPLETED`, the device is done, the page is coherent, the scheduler
   releases `pin_device` → `keep`. Memory leveling owns "may this page move?"; the scheduler owns
   "when is the device using it?" (`pin on submit → coherence-proof on completion → unpin`).

---

## Boot-blocked status
Cannot be boot-proven this session: freestanding boot (B1 uninitialized module globals; B2
bootstrap stage-2 self-host) is blocked. Ships as spec + the interpret-mode pure-logic anchor
`test/01_unit/os/kernel/scheduler/gpu_offload_sched_class_spec.spl` (rank ordering + placement/
backpressure fork + memory_leveling profile-gate/pin lifecycle + sealed-buffer protocol; 16/0).
QEMU scheduler/compositor evidence gates are defined in the companion plan
`doc/03_plan/os/scheduling/cpu_gpu_offload_scheduler_plan.md`.
