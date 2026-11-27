# native-build: SIMPLE_HIR_CACHE=0 disables HIR sharding, so the positional route refuses to start

- **Status:** fix-implemented-verification-pending (P3, bootstrap)
- **Found:** 2026-11-09, Windows, `stage2_new4.exe native-build src/app/mcp/main.spl` with `SIMPLE_HIR_CACHE=0`.

## Observed
```
error: per-file worker pool refused (hir_workers=0 mir_workers=0, need >= 2): HIR sharding is disabled
by SIMPLE_HIR_CACHE=0. No fallback to the two-pass or in-process whole-program build; set
SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 for the explicit single-process build.
```
`src/app/cli/native_build_main.spl:1593` maps `SIMPLE_HIR_CACHE=0` to `hir_disabled_by`, so turning
off the HIR *cache* also turns off HIR *sharding* for the positional (`native-build <file>`) route.
The lane case runner (`run_case_clean.ps1`) sets `SIMPLE_HIR_CACHE=0` and works only because it also
sets `SIMPLE_FILE_WORKERS=0` and uses `--entry-closure`; the same knob on the positional route is a
hard refusal.

## Expected
Either cache-off must not imply shard-off (shards rebuild instead of reusing the cache), or the
refusal must say that the positional route needs the HIR cache and point at
`--entry-closure` + `SIMPLE_FILE_WORKERS=0` as the cache-off path. Owner pick.

## Fix (2026-11-27, fix-implemented-verification-pending)
Because `driver_hir_pipeline_lowering.spl` requires `hir_cache_enabled()` whenever `hir_shard_active()` is true and existing refusal specs (`native_build_pool_refusal_spec.spl`, `native_file_worker_v1_spec.spl`) assert that `SIMPLE_HIR_CACHE=0` refuses pool admission, kept the fail-closed refusal and updated `run_file_worker_pool_v1` in `src/app/cli/native_build_main.spl` via `native_build_hir_disabled_reason_v1` and `native_build_pool_refusal_message_v1` so `SIMPLE_HIR_CACHE=0` refusals state that the positional/per-file route requires the HIR cache to share lowered HIR across workers and direct callers to unset `SIMPLE_HIR_CACHE=0` or pass `SIMPLE_FILE_WORKERS=0` with `--entry-closure` (or `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`) for cache-off compilation.
Specs: `test/01_unit/app/cli/native_build_hir_cache_0_refusal_spec.spl` (4/4 GREEN). Waiting for end-to-end `native-build` CLI verification under `SIMPLE_HIR_CACHE=0`.
