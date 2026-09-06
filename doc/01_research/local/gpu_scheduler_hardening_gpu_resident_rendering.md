<!-- codex-research -->
# Simple GPU Scheduler Hardening and GPU-Resident Rendering

**Status:** selected proposal, 2026-09-05. This preserves the user's design
decision as the repository-local research record; it is not implementation or
hardware-performance evidence.

## Decision

Build a Vulkan-first, no-GC, asynchronous GPU-resident rendering lane by
extending the existing SimpleRing, SOSIX, Engine2D, DrawIR and Object-VM
contracts. Do not create a second scheduler, Future ABI, browser display list,
or GPU memory manager. The strict target is no CPU execution of admitted scene
semantics; native window, input, queue submission, and presentation remain
bounded host-service responsibilities.

## Evidence reconciled with the current tree

- `draw_ir_runtime_queue.spl` currently turns DrawIR into SDN text and drains
  immediately after submit. It is a compatibility adapter, not a resident
  packed/deferred path.
- `host_gpu_event_queue.spl` already owns a bounded queue plus explicit
  submit, complete, and drain phases. Extend those phases; do not invent a
  parallel OS scheduler.
- `SimpleRing<Op,Cpl>` remains the operation lifetime and completion contract.
- Existing GPU full-render and experimental WebScene plans remain separate:
  CPU-semantics/GPU-render is conservative; GPU-semantic islands are additive
  and capability-profiled.

## Required truth labels

Report independently: semantic residency, data residency, submission autonomy,
and scheduling assurance. A short CPU `main`, queue routing, a device-bound
buffer, or an interpreter test is never proof of device execution. Distinguish
submitted, GPU-finished, terminal completion, retirement, presentation queued,
and displayed.

## Selected profiles

`cpu_reference`, `gpu_render`, `gpu_scene_balanced`,
`gpu_scene_required`, `gpu_scene_static_pool`, and
`device_initiated_experimental` are policy names. A required profile rejects
unsupported work rather than silently calling CPU semantic fallback.

## Migration order

1. Correct operation lifetime, provenance, bounded admission, visibility, and
   strict fallback.
2. Add a registered packed DrawIR payload and deferred completion while keeping
   the text/immediate-drain adapter only for compatibility.
3. Qualify a fixed-pool Vulkan 2D showcase with device timestamps and no
   per-frame semantic rebuild/readback.
4. Add GPU-owned event/style/layout/rendering for a declared Web/GUI subset.
5. Add Metal/D3D12 providers and only then qualify optional DGC/ICB/work-graph
   paths.

## Primary references

Existing plans: `doc/03_plan/ui/gpu_full_render_offload_mdsoc_plus_plan.md`,
`doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md`,
`doc/05_design/os/scheduling/cpu_gpu_offload_scheduler_design.md`, and
`doc/05_design/os/scheduling/cpu_gpu_offload_scheduling_gap_map.md`.
External sources selected by the user include Vulkan queue/synchronization and
device-generated-command specifications, Metal ICB, D3D12 indirect/work graph,
Vello, Superconductor, ParPaRaw, Pareas, WHATWG HTML parsing, and GPUDirect
Storage/BaM. They motivate staged capability work; none prove a complete
CPU-free browser.
