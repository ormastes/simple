# Runtime bundle duplicate-symbol gate has unrelated baseline drift
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** open  
**Severity:** P1 release-verification blocker

`sh scripts/check/check-runtime-bundle-duplicate-symbols.shs` scans 27 runtime
files and 1,217 symbols, but currently fails with 12 new duplicate rows and one
stale baseline row (`rt_thread_sleep`). The new rows are pre-existing/concurrent
runtime ownership changes including `rt_dir_create`, file-exists probe helpers,
memory snapshot helpers, and process RSS/HWM helpers; none is the SFFI snapshot
symbol added by this lane.

The gate reports five `same` bodies checked and zero divergent bodies, which
includes the explicitly baselined `spl_dynlib_snapshot_linux` C owner/fallback
pair. The focused SFFI gate independently extracts and byte-compares those two
bodies and passes. Do not refresh the broad baseline mechanically: each of the
12 unrelated pairs needs an owner/link-profile review, and the stale
`rt_thread_sleep` row needs removal only after confirming its producer moved.

**Revalidated 2026-11-02: still plausible because the report title (Runtime bundle duplicate-symbol gate has unrelated baseline drift) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Update 2026-11-03 (fixlane): triaged, 2 real defects fixed, 70 reviewed pairs baselined

Gate before: 41 files / 1678 symbols, 70 new pairs, 2 divergent `same` pairs, 1 stale row. All 72 were classified from the sources and `runtime_compiler.spl` flags, not mechanically:
- REAL DEFECT 1 (divergent): `rt_file_is_regular_no_follow` - runtime_native.c had the Windows long-path fix (`rt_widen_long_path_rc`, 2026-09-25) but runtime.c's copy still used plain UTF-16 conversion, so a lane linking runtime.c would still fail past MAX_PATH. runtime.c now uses the identical body.
- REAL DEFECT 2 (divergent): `spl_dynlib_snapshot_linux` - the runtime_dynload.c owner wraps the sealed memfd in `simple_dynload_unique_snapshot_linux_v1` (monotonic fd floor, because dlopen caches by `/proc/self/fd/N` path and a reused fd number could admit an older mapped object under a newer digest). The runtime_native.c fallback returned the raw memfd. The fallback now has a local twin of the helper; the function body is byte-identical again.
- 70 new pairs, grouped (each group's reason is recorded as a comment block in `scripts/check/runtime_bundle_duplicate_symbols_baseline.txt`): runtime.c/runtime_native.c core-C weak twins (atomic layouts verified identical); runtime_memory.c/runtime_native.c guarded out by `-DSIMPLE_RUNTIME_MEMORY_OWNER=1` which every bundle with runtime_memory.c passes; runtime.c/runtime_legacy_core.c stage4 compat twins; runtime_process.c/runtime_process_owned.c platform-exclusive; runtime_native.c/runtime_timestamp.c weak or TIMESTAMP_OWNER-guarded; runtime_simd_case.c opt-in provider that nothing defines; `rt_thread_sleep` moved pair (stale row replaced). 25 pairs are marked `same` and enforced by the gate; `copy_mem` / `rt_ptr_write_bytes_raw` differ only in pointer-type signature and are not marked `same`.
Gate after: `runtime_bundle_duplicate_symbols_ok=true`, new=0, divergent=0, stale=0. `clang -fsyntax-only` on runtime.c and runtime_native.c clean.
Not done: the Windows `rt_file_is_regular_no_follow` long-path behaviour and the Linux snapshot fd uniqueness were not executed (compile-checked only). VERIFY: Windows lane - create a regular file at a >260-char path and call `rt_file_is_regular_no_follow` via a runtime.c-only link; Linux - `bin/simple test test/01_unit/compiler/backend/runtime_dynload_owner_source_spec.spl` plus a native-all link, and confirm two successive `spl_dynlib_snapshot_linux` calls return distinct, increasing fd numbers.
