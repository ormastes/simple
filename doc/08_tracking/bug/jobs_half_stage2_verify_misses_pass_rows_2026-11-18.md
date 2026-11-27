# jobs=half stage-2 compiler-tests verification misses 4 required PASS rows

Date: 2026-11-18
Host: Windows 11, x86_64-pc-windows-msvc, 24 logical processors
Lane: release/1.0.0 MSVC full 2->3->4 bootstrap (receipt-authorized)

## Symptom

The receipt-authorized full bootstrap (`bootstrap-windows.sh --msvc
--full-bootstrap --mode=dynload --jobs=half --output=build/bootstrap/c41full
--no-mcp --bootstrap-receipt=<planner-admission-v2.env>`) fails at the
stage-2 compiler-tests verification, deterministically:

```
bootstrap-phase-verification: slim stage-2 profile is missing a required PASS row for compiler_cli_build
bootstrap-phase-verification: slim stage-2 profile is missing a required PASS row for compiler_bootstrap_tests
bootstrap-phase-verification: slim stage-2 profile is missing a required PASS row for interpreter_interpreter_tests
bootstrap-phase-verification: slim stage-2 profile is missing a required PASS row for loader_interpreter_tests
VERDICT — ABORTED: stage=scheduling exit=1 signal=none reason=scheduling
```

The stage-2 compiler itself builds and admits fine (1579 modules, 0 failed;
`stage2-admitted` marker published). Only the slim-profile verification of
the compiler-tests campaign fails.

## Evidence

- Two independent `--jobs=half` attempts (clean process table verified before
  attempt 2) failed with byte-identical symptoms. Campaign wall time was
  5243 s and 5270 s respectively — deterministic, not resource-flaky.
- An earlier `--jobs=1` run on the same pinned source passed this exact gate
  ("stage-2 QUALIFY (full slim matrix passed, admitted)").
- Failure manifests: `overlap_observed=true`,
  `stage2_qualification_status=passed`, `failure_reason=stage-engine-failed`.
- The stage-2 compiler-tests phase builds a phase-bound full CLI and
  `simple_test_runner` FROM the admitted stage-2 compiler and runs
  `compiler_cli_build`, `compiler_bootstrap_tests`, `interpreter_*` and
  `loader_*` through them under `--verification-require-test-json`
  (bootstrap-from-scratch.sh ~line 5385). The four missing rows are exactly
  the suites that run through those freshly built tools.

## Red herring: overlap_observed

`overlap_observed=true` is NOT the root cause. Under
`schedule_mode=speculative` (the default when memory is enforceable;
bootstrap-strategy.shs:261) the qualifier intentionally runs concurrently
with the engine, and lines 570-574 flag
`qualification_started < engine_finished` as overlap by construction. The
PASS path (:979) prints `overlap=$overlap_observed` unconditionally. The
failure reason is `stage-engine-failed`, i.e. the slim-profile row check,
not the overlap taint.

## Hypothesis

`--jobs=half` shapes the stage-2 compiler-tests campaign or the
phase-verification task selection such that the four suites above never
record their PASS rows (skipped shard, unmerged per-shard summary, or a
jobs-derived suite partition that omits them). The deterministic ~87-minute
campaign duration across both attempts suggests the suites are not even
attempted rather than attempted-and-flaky.

## Workaround

Run the full bootstrap with `--jobs=1`. It passed this gate historically;
stage-2 build takes ~75+ min serial and the campaigns are the long pole, but
the slim-profile verification records all required PASS rows.

## Repro

1. Mint a planner admission (`produce-bootstrap-planner-admission-v2.shs`)
   against an admitted stage2 parent.
2. `sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap
   --mode=dynload --jobs=half --output=build/bootstrap/c41full --no-mcp
   --progress --bootstrap-receipt=<planner-admission-v2.env>`
3. Observe the failure at ~90 min, right after the stage-2 campaign's
   native-probe receipts, before any stage-3 build starts.

Local evidence bundles (campaign result.env, failure-manifest.env,
stage2-compiler-tests.log) retained in the lane's build tree:
`.build/mcp-release-1.0.0-source/build/c41full-failure-evidence/attempt2|3/`.
