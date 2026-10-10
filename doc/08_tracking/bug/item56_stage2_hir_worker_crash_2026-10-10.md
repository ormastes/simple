# Stage 2 admission HIR worker crash on module path naming (2026-10-10)

Status: OPEN. Blocks current-source pure-Simple compiler admission for Items 5 and 6.

At isolated work branch revision `9050fe878abad386e2bd83b11c771cd95df15083`, the canonical Linux AArch64 bootstrap rebuilt 1,222 modules and entered Stage 2 sanity. The `stage2_module_path_naming.spl` native-build sanity case failed before claiming a module:

`[hir-shard] owner=0/1@0 status=CRASH exit=-139 claimed=0 sealed=0 finished=false`

The aggregate then refused artifact publication with `error: HIR aggregate failure`; the bootstrap exited 2 and refused seed fallback. A second bounded run reused 1,220 modules, rebuilt two, and failed at the same sanity case with the same worker crash. That run set `SIMPLE_HIR_SHARDING=0` on the outer bootstrap command, but the admission child still spawned an HIR shard; this does not show whether the knob was stripped, overwritten, or ignored downstream.

A preceding bootstrap run exited 1 because a runtime C source was edited while its source fingerprint was being captured. The source was committed before both later runs. This is a separate invalidated-run cause, not the HIR crash.

Evidence:
- `build/mini_builds/item56_current_stage2_retry_20261010/bootstrap.log`
- `build/mini_builds/item56_stage2_no_hir_shard_20261010/bootstrap.log`
- `.simple/storage/build/bootstrap/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-failure.log`

Next repair must preserve one source tree, capture the child worker crash stack or equivalent diagnostic, fix the owner, and rerun the exact Stage 2 admission sanity. Do not use the failed candidate as a product runtime or claim Item 5/6 performance from it. This session's three bootstrap verify/fix cycles are exhausted.
