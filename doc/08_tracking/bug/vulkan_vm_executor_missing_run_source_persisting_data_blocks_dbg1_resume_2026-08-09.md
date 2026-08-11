# Vulkan lane has no persisted-arena launch path, so DBG-1 resume is unreachable on Vulkan

- **Date:** 2026-08-09
- **Status:** FIXED 2026-08-09 (P6b) — see "Resolution" at the bottom.
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

## Resolution (P6b, 2026-08-09)

`run_source_persisting_data` added to `VulkanVmExecutor`; `run_source`
redefined as that method with `prior_arena: []`, exactly mirroring the CUDA
shape. New `vulkan_debug_session.spl` + `vulkan_debug_session_conformance_spec.spl`.

### Two of this doc's three "gap" claims were WRONG — corrected for the record

Verified against `7d53bf0a83b` (the very commit that filed this doc) and
against `bfd9284618a`:

- **Claim "Vulkan's `SvmgRunOutcome` has no `out_arena` / `data_off` fields"
  is FALSE.** Both fields were already declared at `:66`/`:67`, with the
  docstring at `:60-65`, at the time of filing. What was true is that no
  construction site in `run_source` ever *populated* them — every one of the
  five `SvmgRunOutcome(...)` literals omitted both fields and the module
  still compiled and passed its gate. So fix step (1) was a no-op; the real
  work was populating the fields, not adding them.
- **Claim the copy "must run to `ARENA_TOTAL_SIZE`" implies the Vulkan code
  was wrong — it was not.** `build_svmg_arena_persisting_data` already used
  the correct absolute-offset form: `copy_start = max(data_off,
  prior_data_off)`, a first loop to `ARENA_DATA_SIZE` (0x10000) and a second
  loop `ARENA_DATA_SIZE..ARENA_TOTAL_SIZE` (0x20000). Those two loops are
  contiguous — `copy_start <= ARENA_DATA_SIZE` always, since
  `build_svmg_arena` panics otherwise — so together they cover
  `copy_start..ARENA_TOTAL_SIZE` and DO include the DBG-1 block at
  `0x1F000`. **This function was left byte-identical.** The two-loop form is
  not a bug to "simplify" into CUDA's single loop; it is equivalent and
  carries the LOG/RECORD-region rationale in its own comment.

Only claim (2) — `run_source_persisting_data` does not exist — was accurate.

### Device evidence

`test/03_system/gpu_lane/vulkan_debug_session_conformance_spec.spl` runs on a
live NVIDIA Vulkan device (`VulkanLaneSession.probe()` returns `""`) and
diffs **20 launches** across 9 of the 10 debug vectors field-for-field
against BOTH the declared table and `ref_vm`. The 10th
(`budget_expiry_while_debugging`) asserts the known lane-layer limitation
rather than skipping, exactly as the CUDA twin does.

### Oracle limits found while sabotage-testing (important)

Reintroducing the absolute-vs-relative trap (`prior_arena[k - data_off +
prior_data_off]`) **does NOT turn this new debug spec red.** Every launch in
a debug-vector session re-assembles the SAME source, so `data_off ==
prior_data_off` and the relative form is arithmetically identical to the
absolute one. The debug vector table therefore CANNOT guard this trap.

The trap IS guarded — by
`test/02_integration/app/tools/notebook/vulkan_exec_spec.spl`'s cross-cell
test, where cell 1 and cell 2 have different code lengths. That test was
confirmed to go RED under the same sabotage and GREEN once reverted. Anyone
re-verifying the absolute-offset invariant must use the cross-cell spec, not
the debug vectors.
