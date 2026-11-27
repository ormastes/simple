# native-build exits 0 with no artifact after a per-file pool refusal

- **ID:** native_build_exit0_no_artifact_after_pool_refusal_2026-11-22
- **Priority:** P1 (a build tool that reports success with no artifact)
- **Status:** fix-implemented-verification-pending (it takes effect only in the next compiler generation)
- **Host:** Windows 11, x86_64-pc-windows-msvc. The Stage 2 compiler was built from release/1.0.0 @ a20233fd230
- **Origin:** `windows_msvc_release_bootstrap_lane_gaps_2026-11-22.md` section 9, "Still open"

## Symptom
The planner admission build (`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`,
`native-build ... --entry-closure --entry src/app/cli/bootstrap_reason_planner.spl -o <adm>/planner.exe`)
logged `error: per-file worker pool refused (hir_workers=0 mir_workers=0, need >= 2)` and
`error: MIR shard aggregate failure ...`. The process still exited 0 with no executable. The
producer only caught it through `planner-build-produced-no-executable`.

## What source reading found
Every route in the source that runs the pool fails closed. `run_file_worker_pool_v1`
(`src/app/cli/native_build_main.spl`) returns `"fail"` on a refusal.
`native_bootstrap_stage3_pool_result_accepts_v1("fail", _)` is false.
`bootstrap_capsule_shard_prepass_routed` returns false, and every caller in
`src/app/cli/bootstrap_main.spl` (coordinator, Stage 3, Stage 4 and positional routes) returns 1.
`bootstrap_main.spl` is byte-identical between a20233fd230 and the release head.
So no single source line returns 0 on this outcome. The exit 0 is unexplained at source level.
One guess, with no evidence behind it, is the bool branch-merge codegen defect of the admitted
capsule (the note in `src/app/cli/bootstrap_native_output_args.spl`). It is a guess only because
this path chains bool returns. It has not been reproduced, and nothing ties it to this failure.

Two other possibilities were checked. Neither explains the exit 0:
- No script under `scripts/` exports `SIMPLE_MIR_SHARD_LINK`, so the "shard child" exclusion
  cannot turn the new gate off for a top-level invocation.
- The producer runs the canonical parent `.exe` directly, not through a wrapper that swallows
  the exit status.

## Fix
There is now a route-level gate in `bootstrap_main.spl` `main`, which no route can bypass. For a
`native-build` that owns an executable it checks the artifact after the route returns: exit 0 plus
an explicit `-o` path that does not exist now becomes exit 1 with
`error: native-build finished with exit 0 but produced no artifact at <path>; failing closed`.
- Ownership is decided before the route runs (`bootstrap_native_build_artifact_owner_v1`).
  Excluded: coordinator workers (`SIMPLE_NATIVE_BUILD_WORKER=1`), shard and role children,
  the MIR export-summary producer, grouped children, help/list/removed-bundle actions, and
  object/archive/shared output.
- The predicate `bootstrap_native_build_missing_artifact_v1` is in
  `src/app/cli/bootstrap_native_output_args.spl`. It is i64-valued, following that file's
  rule about the bool-merge defect.
- Successful builds are unchanged: the gate fires only when the code is 0 and the file is absent.

## Specs
- Reproduction plus generalization: `test/01_unit/app/cli/bootstrap_native_build_missing_artifact_spec.spl`.
  It covers the exact case (exit 0, owned, absent), plus present artifact, nonzero codes,
  non-owners and no `-o`, and the main wiring.
- Related: `test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl` pins the
  worker-coordinator twin.

## Verification pending
The spec runs only on a compiler deployed after this change. Two checks follow the next
Stage 2 build. First, a pool refusal (low reported memory with the per-file default) must exit
nonzero. Second, the producer must report `planner-build-failed`, not
`planner-build-produced-no-executable`. If the gate fires, its message proves the underlying
exit-0 path exists. That path then needs its own root cause, starting with the bool-merge suspect.
