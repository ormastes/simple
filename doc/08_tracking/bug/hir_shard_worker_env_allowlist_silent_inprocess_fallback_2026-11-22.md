# HIR shard worker env allowlist silently degrades to in-process HIR

- **Date:** 2026-11-22
- **Status:** fix-implemented-verification-pending
- **Severity:** P2
- **Updated:** 2026-11-25

## Symptom

Unknown `SIMPLE_*` keys in the build environment (for example `SIMPLE_PHASE_RSS`) make the HIR worker pool refuse to start. HIR then runs in-process with no hard error, so a whole build silently loses HIR parallelism.

## Evidence

The allowlist lives in `src/app/cli/worker_hir_profile_v1.spl`. Observed during Phase 3 full-CLI builds: setting an extra `SIMPLE_*` key changed the build from sharded HIR workers to a single in-process HIR pass with no diagnostic naming the key.

## Repro

Run a Phase 3 native-build with `SIMPLE_PHASE_RSS=1` exported alongside the normal build env; HIR runs in-process.

## Workaround

Unset every `SIMPLE_*` key not in the allowlist before launching the build.

## Fix direction

Fail closed with an error naming the offending key, or ignore keys that do not affect worker semantics.

## Fix implemented (2026-11-25)

1. **Fail-closed explicit `SIMPLE_HIR_SHARDING=1` refusal**: `native_build_hir_refusal_runs_serial_v1` and `native_build_hir_refusal_blocks_v1` (`src/app/cli/native_build_hir_warmup_outcome.spl`) plus callers in `src/app/cli/native_build_main.spl` (`run_native_build_worker_inner` and `native_build_focused_capsule_shards_v1`) now fail closed with `hir_run.blocked_reason` (even under `--go-to-end`) instead of falling back to serial HIR when `SIMPLE_HIR_SHARDING=1`. In addition, `native_build_focused_capsule_shards_v1` now honors policy `2` (`SIMPLE_PARSE_SHARDING=0` + `SIMPLE_HIR_SHARDING=1`) via `!= 0` and validates canonical SCV authority via `native_build_hir_only_scv_error_v1`, while auto/default sharding retains serial fallback.
2. **Allowlist & Phase C tool-row keys**: `src/app/cli/worker_hir_profile_v1.spl` now admits safe diagnostic/retry keys (`SIMPLE_PHASE_RSS`, `SIMPLE_ICE_CRASH_RETRIES` in base), host/headroom/RSS-cap keys (`SIMPLE_HOST_MEM_RESERVE_FREE_MIB`, `SIMPLE_HOST_WORKER_MEM_MIB`, `SIMPLE_HOST_MAX_THREADS`, `SIMPLE_BOOTSTRAP_WORKER_MEM_MIB`, `SIMPLE_BUILD_MEMORY_ALLOW_COMMIT_WITNESS`, `SIMPLE_PROCESS_TREE_RSS_CAP_KIB`, `SIMPLE_PROCESS_TREE_RSS_INTERVAL_MS` in both `stage3` and `tools`, plus `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` in `stage3`), and `SIMPLE_STAGE3_DIRECT_THREADS` in Stage 3-only (`stage3`). All `base` and `tools` tool-row keys are synchronized with `scripts/bootstrap/phase-c-backend-commands.shs` (`bootstrap_phase_c_tool_row_environment_keys`).
3. **Remaining**: live native Phase 3/4 bootstrap execution on target host with `SIMPLE_PHASE_RSS=1` and `SIMPLE_HIR_SHARDING=1` pending deployed/rebuilt compiler binary.
