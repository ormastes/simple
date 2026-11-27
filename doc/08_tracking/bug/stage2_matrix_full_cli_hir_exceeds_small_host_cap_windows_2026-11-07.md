# Stage 2 matrix `compiler_cli_build` exceeds the small-host one-worker cap on a 32 GiB Windows host

Date: 2026-11-07
Host: DESKTOP-5A4V03J, Windows 11, 33,195,332 KiB RAM (`config/host/DESKTOP-5A4V03J.sdn`, `mem_reserve_free_mib: 10240`)
Lane: `scripts/bootstrap/bootstrap-windows.sh --full-bootstrap --stop-after-stage2 --mode=dynload --jobs=half --backend=cranelift`
Source of the failing run: worktree `D:/dev/simple-s2b-20261107` at `aa03b017ad3`
Status: fixed on `release/1.0.0` by `fe52a1431e6` for the default (slim, delegated) matrix; the full-CLI profile remains unfit for this host class (open, see "Still open")
Related: `tree_rss_whole_build_floor_blocks_32g_hosts_2026-11-05.md` (small-host mode was its fix),
`worker_advice_lexical_false_roots_2026-11-06.md` (why the tool rows pin `SIMPLE_FILE_WORKERS=0`)

## Observation (reproduced twice)

Stage 2 builds and is ADMITTED. The post-admission phase-verification matrix then
fails in `compiler_cli_build`:

```
stage2-compiler-tests tree RSS cap: 14126616 KiB, build-threads=1 (whole-build phase:
workers 1 (requested 4, host budget fits 1, timeout scale x4), cap 14126616 KiB =
SMALL-HOST MODE: 1 worker under host budget (one-worker requirement 29360128 KiB =
base 4194304 KiB + worker floor 16777216 KiB x 150% exceeds it), host budget
14126616 KiB (3/4 of available 18835488 KiB; host RAM via proc-meminfo), ...
bound small-host-one-worker)
status=rss-cap-exceeded  exit_status=88
max_rss_kib=14126616  peak_rss_kib=14178236  samples=26920  observer_backend=win32-job-object
```

`compiler_cli_build.log`: entry `src/app/cli/_CliMain/main_and_help.spl`, closure
**3069 modules**, single in-process frontend (build-threads=1). Killed in
`phase=hir` at module **1527/3069** after `elapsed_ms=2811721` (~47 min). The
frontend policy rows were `SIMPLE_SHARD_MEM_CLAMP=1`, `SIMPLE_PARSE_SHARD_MAX=1`,
`SIMPLE_PARSE_SHARD_WORKER_KB=1650000`, `SIMPLE_HIR_SHARD_WORKER_KB=3000000`,
`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=3000000`.

Logs:
`D:/dev/simple-s2b-20261107/.simple/storage/build/bootstrap/logs/x86_64-pc-windows-gnu/stage2-compiler-tests.log`,
`.../stage2-compiler-tests/x86_64-pc-windows-gnu/verification/logs/compiler_cli_build.log`, `summary.env`.

## Root cause

1. **The matrix built the FULL CLI** (3069-module closure) in one process. The
   Phase C tool build (`bootstrap_phase_c_run_tool_build`,
   `scripts/bootstrap/phase-c-backend-commands.shs`) pins `SIMPLE_FILE_WORKERS=0`
   (two-pass route; the per-file pool fails closed with
   `FILE-WORKER-E-CLOSURE-INCOMPLETE` on this entry's cross-module AOP advice), so
   every module's HIR is retained in the one frontend until MIR lowering. That is
   by construction, not a per-module leak: MIR lowering of the two-pass route
   consumes the whole-program HIR. Measured HIR growth is roughly linear: 14.18 GB
   at 50 % of HIR here; the same comment block records a full-CLI worker starting
   MIR at ~19.3 GiB (run 10, 2026-11-06) and 12.6 GB at 73 % HIR for the 2546-module
   closure (2026-10-13). A cold full-CLI frontend therefore needs ~19-20 GiB on its
   own, which a 32 GiB host with a 10 GiB reserve cannot give one process.
2. **The cap is correctly computed.** `x 150%` is the runaway margin, not
   "x 15": `bootstrap_tree_rss_whole_build_plan`
   (`scripts/bootstrap/lib/tree-rss-policy.shs`) prices one worker at
   `base 4194304 + floor 16777216 x 150% = 29360128 KiB`; the host budget is
   `min(33195332 x 75 %, 3/4 x MemAvailable 18835488) = 14126616 KiB`, so
   small-host mode runs exactly one worker capped at the budget. The low
   MemAvailable reflects concurrent load on the host (an AVX perf run was
   active); even fully idle, 3/4 of ~28 GiB available (~21 GiB) is at the edge of
   the ~19-20 GiB cold full-CLI frontend plus coordinator.
3. **Ruled out:** `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` leaking from
   `candidate_frontend_admission.shs`. That default (PR #7328) is set inside
   `candidate_frontend_smoke_profile() ( ... )`, a subshell, so it cannot reach
   the matrix. Even an operator-exported `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` does
   not change this row: it only gates the per-file pool
   (`native_bootstrap_stage3_per_file_selected_v1`,
   `file_worker_module_scoped_selected_v1`), which the row already disables via
   `SIMPLE_FILE_WORKERS=0`. The HIR/MIR shard pool is not available either: at
   build-threads=1 (the only count small-host mode admits) the build runs
   in-process, and in the two-pass process route each MIR shard worker still
   builds its own whole-program HIR first (the ~19.3 GiB start above).

## Fix

`fe52a1431e6` ("fix(bootstrap): slim delegated Stage2 verification CLI",
2026-11-07 11:47, on `release/1.0.0`, NOT in `aa03b017ad3`) makes
`bootstrap_phase_select_compiler_cli` build `src/app/cli/bootstrap_verify_main.spl`
(cache `verification-cli`) instead of the full CLI whenever
`phase=stage2`, `--profile=slim` and the Stage 2 test delegate is on — which is
the default Windows path (`bootstrap-from-scratch.sh` passes `--profile=slim`
for the normal strategy; `BOOTSTRAP_STAGE2_TEST_DELEGATE` defaults to 1). The
slim entry imports only SCV admission, the explicit-driver lookup and
`process_run_inherit`. Approximate static import closure (scratch walker,
same method for both): slim CLI 173 files vs test runner 144; the test runner's
measured real closure is 265-319 modules at a 2.5-2.9 GiB peak, so the slim CLI
row is expected at a few GiB, far below the 14.1 GiB small-host cap.
Contract pinned by `scripts/check/check-bootstrap-slim-verification-cli.shs`.

Re-run needed on this host from a worktree that contains `fe52a1431e6`; the
`summary.env` then carries `compiler_cli_entry=src/app/cli/bootstrap_verify_main.spl`
(the failing run's summary has no `compiler_cli_entry` row, confirming the
pre-fix code). Not re-run here: the host was serving an AVX perf run
(MemFree 15.8-19.2 GB) during this analysis.

## Still open

`--profile=full`, `SIMPLE_BOOTSTRAP_STRATEGY=full`, or
`BOOTSTRAP_STAGE2_TEST_DELEGATE=0` still build the 3069-module full CLI with
whole-program HIR in one process, which does not fit a 32 GiB host. Closing that
needs the per-file pool to close cross-module AOP advice
(`worker_advice_lexical_false_roots_2026-11-06.md`) so HIR is released per file,
or HIR retention bounded in the two-pass route. Until then the small-host plan
burns ~47 min before the exit-88 kill; a fail-fast refusal for the full-CLI row
in small-host mode would be cheaper, but should key on measured evidence rather
than a guess.
