# Stage-2 verification matrix: HIR shard workers exit -2 on Windows, full-CLI closure never aggregates

Status: OPEN. Owner: bootstrap phase verification.

## Summary

On the release_phase3 qualification lane (worktree C:/p3, branch tip a649ea4acb9,
later 54a1397eb49), the stage-2 compiler builds and is ADMITTED cleanly, and the
bootstrap sanity / struct-receiver / stage3-materialized-consumer gates all PASS.
The stage-2 verification matrix (`--strategy=adhoc --incremental-unlimited
--full-bootstrap --stop-after-stage2`, profile=slim) cannot complete on this
host: the required `compiler_cli_build` row dies reproducibly with an HIR
aggregate failure, which cascades into `test_runner_build` FAIL,
`stage2_tool_workers` FAIL, ~14,075 `module_compile` rows BLOCKED, and the
required delegated suite rows (`compiler_bootstrap_tests`,
`interpreter_interpreter_tests`, `loader_interpreter_tests`) never executing
(slim profile reports them missing-PASS). The lane therefore cannot reach the
stop-after-stage2 terminal state and Phase 3 cannot start from this matrix.

Host: x86_64-pc-windows-msvc, Windows/Git Bash, LLVM 23.1.1
(`C:\Users\user\.simple\toolchains\llvm-msvc-23.1.1\clang+llvm-23.1.1-x86_64-pc-windows-msvc`),
admitted stage-2 candidate sha256 86ff7375e265a8510e42f16c0fd687eaf2d100ed72c59103f85d800920eba092
(first admission on this line: a6b18fd84c5f88a48afa0beaf61434f39678155fb0f0ed01127db25a28cf5078).

## Reproduction

Two full clean-cache attempts, both with a fresh SCV snapshot and with the
stage-2 MC/DC delegation waiver atoms set
(`SIMPLE_MCDC_OFF_WAIVER_REASON/REVIEWER/REVIEW_ID/VERSION`; matrix header
records `test_execution=delegated-seed`, `test_execution_mcdc=off-waived`):

1. 2026-10-11 ~23:11-23:45 local (wrapper run started 21:59:36).
2. 2026-10-12 01:41-01:58 local, after `rm -rf build/scv
   build/bootstrap/stage2-compiler-tests .../stage2-native-cache` (run started
   00:37; SCV snapshot freshly re-captured by the wrapper's scv-prime sanity
   probe at 01:10, so the snapshot was complete and consistent).

Both attempts: `compiler_version` row PASSes; `compiler_cli_build` (full-CLI
closure, 2538 files, compiled out of the scv snapshot copy) reaches mid-parse
— attempt 1 around 1783/2538 files, attempt 2 around 1913/2538, zero module
failures — then the HIR shard reports:

```
[hir-shard] owner=0/1@0 status=BLOCKED exit=-2 claimed=0 sealed=-1 finished=false
[hir-shard] inventory incomplete rows=-1 policy_fail_fast=false
[hir-shard] completed_workers=0 failed_workers=2 failed_modules=0 unfinished=-1
error: HIR aggregate failure; final worker and artifact publication blocked
```

Module-compile rows then run with EMPTY logs (0-byte compile.logs under
`stage2-compiler-tests/.../module-diagnostics`) and the aggregate never forms.
Final summary rows: compiler_version=PASS, compiler_cli_build=FAIL,
test_runner_build=FAIL, stage2_tool_workers=FAIL, module_compile_unexecuted=
BLOCKED, compiler_bootstrap_tests/interpreter_interpreter_tests/
loader_interpreter_tests=UNSUPPORTED (delegated route never receives tools);
slim profile rejects: "missing a required PASS row" for cli, runner and the
three suites. `rejection.env` records status=rejected.

Last files at the parse frontier when the shard died (parallel workers, not a
single deterministic file): attempt 1 `src/compiler/50.mir/hwir/zca_rv64_*.spl`
region plus `src/compiler/90.tools/lint/param_object_rules.spl`; attempt 2
`src/compiler/35.semantics/lint/*.spl`, `src/compiler/40.mono/monomorphize/
types.spl`, `src/compiler/70.backend/linker/lib_smf_reader.spl`,
`src/compiler/90.tools/lint/param_object_rules.spl`.

## Suspected leads

- Worker processes killed by resource policy: the wrapper runs with a
  process-tree RSS cap of 5,859,375 KiB (default policy, 14-16 workers,
  "hard ceiling" ~6.8-7.3 GB) while the stage-2 compiler workers each hold
  tens of MB during a 2538-file closure parse. `exit=-2` with
  `failed_modules=0` (workers die without reporting a failing module) is
  consistent with an external kill rather than a typed compile error.
  The host was under heavy concurrent load from other qualification lanes
  during both attempts; per-attempt parse throughput was identical (~3.3
  files/s) and the die point scales with wall-clock contention, not with a
  specific source file.
- Stage-2 compiler crash on specific closure modules: less likely (no
  single-file determinism, zero `failed_modules`, different frontier files
  across attempts), but not ruled out — no worker stderr is captured anywhere
  under the evidence tree, which is itself a observability gap:
  `compiler_cli_build.max-rss-kib` reads `unavailable` and the killed workers
  leave no crash dump or stderr file.

Knobs tried: `BOOTSTRAP_VERIFY_NATIVE_INTERNAL_TIMEOUT=2400` (widen the 600 s
per-build internal timeout) — the retry was abandoned in consolidation before
reaching the matrix, so the timeout hypothesis is UNVERIFIED. Reducing
`--threads`/module-workers or raising the RSS cap for the matrix tool builds
is untried.

## Why this blocks Phase 3

The managed Phase 3 resume requires the stage-2 verification matrix evidence
in addition to the stage-2 admission receipt. The admission receipt itself is
published and intact; the matrix rejection is the blocker. The standalone
planner-admission producer
(`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`) additionally
re-validates the complete stage-2 authority (sanity + provenance sidecars);
its exact behavior against this tree is recorded in the qualification report.

## Evidence

All under C:/p3/build/bootstrap:
- stage-2 admission: `stage3/x86_64-pc-windows-msvc/stage2-admitted/admission.env`
  (plus `stage2-admitted.prior-attempt-*` archives).
- Attempt 2 (clean): `stage2-compiler-tests/x86_64-pc-windows-msvc/verification/`
  (summary.env, logs/compiler_cli_build.log, campaign.touhSr),
  `logs/x86_64-pc-windows-msvc/stage2-compiler-tests.log`, fresh snapshots in
  `build/scv/snapshots/scv-revision-v1-4c09796b...` and `-91a8b686...`.
- Attempt 1 (interrupted SCV era): same paths pre-clean; its stale-snapshot
  poisoning was eliminated as the cause by attempt 2's clean-cache reproduction.
- Wrapper consoles and progress: `logs/x86_64-pc-windows-msvc/bootstrap-progress.log`,
  `.../bootstrap-preflight.log` (PASS, 5 checks).
