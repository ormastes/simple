# D1's src/lib/common/svmg module is not present on shared main, blocking B3 in-tree verification

Date: 2026-08-07
Found by: Task B3 (cuda_vm per-launch executor,
doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md §3)

## Summary

B3's task brief states dependencies A3, B1, D1 are "all already landed."
Empirically, at every point checked during this task's session (multiple
checks across ~10 minutes of a repeatedly force-pushed/rebased shared
working copy, `git log --oneline -1` returning a different commit SHA each
time), `src/lib/common/svmg/` (Task D1: `opcodes.spl`, `sgp.spl`,
`mailbox_const.spl`, `assembler.spl`, and Task D2's `ref_vm.spl`) was
**absent** from the checked-out tree, and `git merge-base --is-ancestor
<known-good-D1-commit> HEAD` / `... origin/main` both returned false — the
commit that has these files (`c2f18eec42e`, confirmed via `git log --all
--oneline -- src/lib/common/svmg/opcodes.spl`) is not an ancestor of either
current `HEAD` or `origin/main` at time of writing.

`doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`'s own
"Status" section (as last updated) independently corroborates this: it
lists A1, A2, B0, C1 as landed and does not mention D1/D2/D3/B1 at all.

Separately, `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl` (Task B1)
was observed to be a **0-byte file** in the shared tree at one point during
this session (not caused by this task -- B3 never wrote to that path) --
consistent with a concurrent sibling session mid-write/mid-checkout on the
same shared working copy, per the repo's documented shared-WC hazards
(`.claude/memory/reference_shared_wc_environment_traps_2026-07-30.md` and
neighbors).

## Impact on B3

- `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl` (this task's
  deliverable) imports `std.common.svmg.assembler`, `std.common.svmg.sgp`,
  `std.common.svmg.mailbox_const`, and `std.gc_async_mut.gpu_lane.cuda_lane_session`
  -- none resolvable in the checked-out tree at commit time, so
  `bin/simple lint`/`bin/simple test` against this file cannot currently
  produce a real pass/fail signal in this repo checkout.
- The D3 conformance table (`test/fixtures/svmg/conformance_vectors.spl`,
  `test/02_integration/svmg/conformance/conformance_suite_spec.spl`) is
  likewise unresolvable, so this task could not run the full ">=40 vector"
  in-repo conformance sweep the plan's Verify line requires.

## What was verified instead (see B3 task report for detail)

The SVM-G opcode encoding, SGP header layout, and GMB-1 arena layout are
fully documented in the D1/D2/A2 source (read into context before this gap
was discovered) and are stable, numeric, byte-level contracts -- not
behavior that depends on the module being *importable* in this checkout.
The checked-in `svmg_cuda_kernel.ptx` device interpreter was verified
against that documented encoding using a standalone CUDA-driver-API C
harness (bypassing the Simple module system entirely), on real GPU
hardware (NVIDIA RTX A6000, sm_86), for representative vectors including
the mandated budget-exhaustion -> `0xDEAD0000` case. This is real evidence
for the *kernel's* correctness, but is not a substitute for running the
actual, authoritative D3 vector table once D1 is reachable from this
checkout.

## Unblock condition

D1 (and D2/D3/B1, all listed as prerequisites) need to actually be present
on `main`/`origin/main` as seen by `git log -- src/lib/common/svmg/`. Once
that is true, re-run:

```
bin/simple lint src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl
bin/simple test test/02_integration/svmg/conformance/conformance_suite_spec.spl
```

and drive the same table through `CudaVmExecutor.run_source` (a small
system spec, not yet written, is the natural home for this -- see B3
report) to get the full 44-vector pass/fail against the on-device
interpreter rather than the standalone C harness's 3-vector spot check.
