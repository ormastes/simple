# `VulkanVmExecutor.run_source` clobbers arena DATA on every call — unusable as-is for K6's cross-cell persistence contract

**Found while implementing:** Stream K, task K6 (`VulkanExec` notebook executor),
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`.

## What's wrong

`src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl:191-224` (`me
run_source(...)`) is the only public entry point `VulkanVmExecutor` offers for
running a program. Internally it calls `build_svmg_arena(code, step_budget,
entry_pc)` (line 90), which does:

```
var arena = _zero_bytes(ARENA_TOTAL_SIZE)
```

i.e. it builds a **fresh, fully-zeroed** 128 KiB arena for every call, writes
the new header + code into it, and then `run_source` uploads that whole
zeroed-except-header/code buffer to the device
(`self.session.arena_write(arena)`, line 198) — unconditionally overwriting
whatever the previous dispatch had left in the arena's DATA region.

This is correct and intentional for `VulkanVmExecutor`'s own contract
(stateless, one-shot conformance-vector runs — see
`test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl`, which runs
~30 independent vectors back to back and explicitly wants each one isolated).

## Why it blocks K6

`doc/05_design/app/tools/notebook_lanes_architecture.md` §4.5 requires, for
the notebook Vulkan lane:

> `execute_cell`: write SGP blob, one dispatch, fence, drain LOG/RECORD ⇒
> outputs. Arena DATA persists across dispatches ⇒ incremental state, same
> model as CUDA per-launch.

`run_source`'s build-a-fresh-zeroed-arena-every-call behavior makes that
impossible to satisfy by calling `run_source` directly: a second
`execute_cell()` would always see a data region that was scrubbed by the
first call's own `run_source`, never actual carried-over state.

## Workaround used in K6 (not a fix to this file)

`src/lib/nogc_sync_mut/notebook/vulkan_exec.spl` does **not** call
`VulkanVmExecutor.run_source`. It instead composes the same already-exported
building blocks `vulkan_vm_executor.spl` itself uses
(`std.common.svmg.assembler.svmg_asm`, `std.common.svmg.sgp.{sgp_header_new,
encode_sgp_header, SGP_HEADER_SIZE}`, `VulkanLaneSession` directly) and keeps
its own `last_arena: [u8]` copy across `execute_cell()` calls: each cell
overlays a freshly assembled header+code onto a *copy of the previous
readback* (not a freshly zeroed buffer), resets only the transient
sentinel/LOG/RECORD regions, dispatches, and persists the new readback for
the next cell. This is composition over the existing public
`VulkanLaneSession`/pure-function API, not a reimplementation of SFFI/session
internals.

## Suggested real fix (not done here — out of K6 scope)

Give `VulkanVmExecutor` (or `build_svmg_arena`) an optional "preserve prior
DATA" mode — e.g. `run_source_preserving_data(source, step_budget, entry_pc,
prior_arena: [u8])` — so a future caller doesn't have to re-derive the
byte-layout logic K6 duplicates here. Low priority: only one caller
(`VulkanExec`) needs it today.
