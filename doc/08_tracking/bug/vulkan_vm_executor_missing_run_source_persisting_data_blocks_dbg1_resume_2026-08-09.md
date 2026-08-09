# Vulkan lane has no persisted-arena launch path, so DBG-1 resume is unreachable on Vulkan

- **Date:** 2026-08-09
- **Status:** OPEN
- **Component:** `src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl`
- **Found by:** P6, while writing `vulkan_debug_session.spl` as the mirror of
  the (landed, device-verified) `cuda_debug_session.spl`.

## Symptom

`vulkan_debug_session.spl` **was not written**, because the lane API it would
delegate to does not exist. DBG-1 "break, inspect, resume" is therefore
unavailable on the Vulkan backend even though the Vulkan *kernel* now
implements the full DBG-1/PROF-1 contract.

## The gap

DBG-1 resume works entirely through the persisted arena: the DBG-1 block at
`0x1F000..0x20000` rides forward from one launch to the next inside the
copied arena region. On CUDA that is `CudaVmExecutor.run_source_persisting_data`,
whose `SvmgRunOutcome` carries `out_arena` and `data_off` back to the caller.

On Vulkan:

- `build_svmg_arena_persisting_data` **exists and is exported**
  (`vulkan_vm_executor.spl:137`, `:278`) — but has no caller.
- `run_source_persisting_data` **does not exist**. `run_source` (`:238`)
  calls plain `build_svmg_arena` (`:244`) unconditionally.
- Vulkan's `SvmgRunOutcome` has **no `out_arena` / `data_off` fields**, so
  even a successful launch cannot hand the arena back for the next one.

Note the misleading state of the file: the docstrings at `:63` and `:65`
already describe feeding values "back into `run_source_persisting_data`", as
though the method were present. It is not. A reader (or an agent) skimming
those comments will conclude the capability exists.

## Impact

- No `vulkan_debug_session.spl`, so no Vulkan half of the unified
  debug/profile capability.
- The Vulkan kernel's DBG-1/PROF-1 code — restore, breakpoint scan,
  single-step, save-state — is **completely unexercised on device**. It has
  been validated only by `spirv-val` and by mirroring `ref_vm.spl`. The two
  green Vulkan gates run with `DBG_FLAGS == 0` and prove *inertness only*.
  Treat the Vulkan debug path as unverified until this is closed.

## Fix

Port the CUDA shape verbatim, since the arena layout is byte-identical:

1. Add `out_arena: [u8]` and `data_off: i64` to Vulkan's `SvmgRunOutcome`.
2. Add `me run_source_persisting_data(source, step_budget, entry_pc,
   prior_arena, prior_data_off)`, building via the already-present
   `build_svmg_arena_persisting_data` and reading the arena back after the
   fence.
3. Redefine `run_source` as that method with `prior_arena: []`, preserving
   its stateless-per-call contract (the D3 conformance spec depends on it).
4. Then mirror `cuda_debug_session.spl` to `vulkan_debug_session.spl` and
   `cuda_debug_session_conformance_spec.spl` to its Vulkan twin.

**Watch the known trap while doing (2):** SVM-G STORE/LOAD and the DBG-1
block address the arena by ABSOLUTE byte offset, never relative to
`data_off`. This bug has been introduced and fixed 3+ times in this repo,
most recently in this very file's persisted-arena copy. `copy_start` must be
`max(data_off, prior_data_off)` and the copy must run to `ARENA_TOTAL_SIZE`
so the DBG-1 block at `0x1F000` is included.
