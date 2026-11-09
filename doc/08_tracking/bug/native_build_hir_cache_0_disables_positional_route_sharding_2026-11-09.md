# native-build: SIMPLE_HIR_CACHE=0 disables HIR sharding, so the positional route refuses to start

- **Status:** open (P3, bootstrap)
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
