# Runtime bundle duplicate-symbol gate has unrelated baseline drift

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
