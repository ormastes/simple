# `rt_*` call-site ratchet regression in two stdlib domain trees

- **Filed:** 2026-09-05
- **Status:** OPEN — regression against a recorded baseline, NOT re-baselined
- **Oracle:** `test/03_system/plan_acceptance/perf_checklists_spec.spl`
  "measures current rt_* call-site count per domain tree against the plan's
  named baseline" (RED)
- **Plan:** `doc/03_plan/infra/perf_umbrella/perf_checklists.md` (AC-9 rows)

## Measurement

The oracle iterates the plan's `AC9_ROWS` and, for each row with a
non-negative baseline, requires `measured <= baseline`. Counting method is the
spec's own (unchanged):

```
grep -r 'rt_' <path> --include='*.spl' | grep -v '^ *//' | wc -l
```

Measured 2026-09-05 on `src/compiler_rust/target/debug/simple`
(debug Rust seed, 120103640 bytes, mtime 2026-09-04 18:13):

| domain tree | baseline | measured | delta |
|---|---|---|---|
| `src/lib/nogc_sync_mut` | 7974 | **10230** | **+2256 (+28.3%)** |
| `src/lib/nogc_async_mut_noalloc` | 358 | **395** | **+37 (+10.3%)** |

Two further rows named by the plan (`src/lib/nogc_sync_mut/src/net`,
`.../database/pure_sql`) do not exist on disk and are skipped silently by the
oracle — worth noting because it means the AC-9 row set is itself partly stale.

## Why it is filed rather than fixed or re-baselined

This is the `rt_*` direct-call-site population the perf umbrella exists to drive
DOWN; `.claude/rules/vcs.md` already carries a separate push-tier ratchet
(`check-no-direct-rt.shs`) over `src/**` product code for the same reason.
Raising the baseline to 10230 would convert a 28% regression into a green
checkbox and destroy the ratchet's only function. The oracle is correct and the
red is honest.

The regression is also not attributable to the 2026-09-05 plan-acceptance pass:
that session's only `src/lib` edit was the `serial_close` double-close guard in
`src/lib/nogc_sync_mut/io/serial_sffi.spl`, which adds no `rt_*` call site (it
adds a guard that *avoids* one). The +2256 predates it.

## Next step

Bisect the `src/lib/nogc_sync_mut` growth to find which lanes added direct
`rt_*` call sites, and route them through the provider surfaces the allowlist
(`scripts/check/no_direct_rt_allowlist.txt`) already recognises. Do not
regenerate the AC-9 baseline without reading that diff.
