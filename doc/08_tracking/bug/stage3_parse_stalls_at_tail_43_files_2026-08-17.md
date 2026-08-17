# Stage-3 parse costs >547s on its last 43 files (superlinear, not a hang)

- **Filed:** 2026-08-17
- **Severity:** P1 — blocks stage 3, therefore blocks stage 4 and any redeploy
- **Status:** OPEN, observed live
- **Phase:** bootstrap stage 3, task 1 of 6 (`phase=parse`)

## Summary

With the `Dict.clear()` MIR-lowering fix in the tree (`15c3131f644`), stage 3 no
longer dies with the 78 false enum-payload owner conflicts — it gets **past** the
point where the previous seven attempts failed. It now stalls instead: the parse
phase completes 576 of 619 files quickly, then spends **>547 seconds making zero
progress on the remaining 43**.

This is a **cost problem, not a hang**. The process is demonstrably working.

## Measured evidence

From `build/bootstrap/bootstrap-progress.log` (30s sampling), single run:

| files | elapsed | per-file |
|---|---|---|
| 0 → 160 | ~120s | ~0.75s |
| 160 → 320 | ~60s | ~0.38s |
| 320 → 448 | ~30s | ~0.23s |
| 448 → 576 | ~30s | ~0.23s |
| **576 → 577** | **>547s and still running** | **>547s** |

- **19 consecutive samples** report `done=576 total=619 remaining=43`, spanning
  `elapsed_s=852` through `elapsed_s=1399`.
- Process state `R`, **753 CPU ticks per 10s** (~75% of one core). Not blocked,
  not swapping, `wchan` empty.
- **Single-threaded**: `nlwp=1`.
- RSS essentially flat: **~512 KB per 10s** (~51 KB/s), after climbing at
  ~1 GB per 30s during the healthy part of parse. Total 7.97 GB.
- `majflt=6` over the whole run — not I/O bound.

So per-file cost rose by more than **2000×** between file 448 and file 577.
Allocation stopped while CPU stayed pinned: the work is compute, not growth.

## What is NOT the cause

- **Not a hang / deadlock.** CPU advances monotonically; state is `R`, not `D`/`S`.
- **Not memory pressure.** 37 GB available at the time; RSS flat, 6 major faults.
- **Not I/O.** No file descriptors open on `.spl` during the stall.
- **Not the file named in the progress line.** `current=` is only written at the
  64-file reporting boundary (`driver_source_pipeline_parsing.spl:275`,
  `progress_parse_done % 64 == 0`), so it is **stale by up to 63 files**. The
  reported `src/std/nogc_sync_mut/sffi/dynamic.spl` is an ordinary 263-line file
  and is almost certainly NOT where time is going. The real offender is one of
  files 577–619, identity currently unknown.

## Probable relation to an existing bug

This looks like the same superlinear term already filed for the linter in
`lint_timeout_hwir_zca_rows_2026-08-17.md`, where cost is driven by declaration
CONTENT rather than count, grows superlinearly within a file, and terminates
without hanging (2 functions of `zca_rows.spl` cost 210s; 8 functions exceeded
2400s). If parse and lint share that path, this is one defect with two symptoms.
**Unproven** — stated as a hypothesis, not a finding.

## Why it is not diagnosed yet

Attach-based profiling is blocked on this host, exactly as recorded in the lint
bug: `ptrace_scope=1` and `perf_event_paranoid=4`. No `perf`, no `gdb` attach.
That is the blocker on locating the superlinear term for both bugs.

## Reproduce

```sh
sh scripts/bootstrap/bootstrap-from-scratch.sh --progress --progress-interval=30
# watch build/bootstrap/bootstrap-progress.log for a run of identical
# done=<n> samples while tree_cpu_pct stays ~80
```

## Next steps (in cost order)

1. **Identify the offending file.** Parse files 577–619 individually with a
   stage-2 binary and time each; the closure order is deterministic, so the tail
   set is stable. Cheapest real progress available.
2. **Make the stall visible without profiling.** `log_build_progress` reports
   every 64 files, which is why a 9-minute stall inside one batch looks
   identical to normal work. Report per-file (or on a time trigger) during parse
   so the offender names itself. Note `b4872f73454` already routes these events
   to stdout, so the stage log will carry them once a binary is rebuilt from
   that commit.
3. Only then chase the superlinear term itself, jointly with the lint bug.

## Related

- `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md` — same shape,
  same host-level profiling blocker.
- `b4872f73454` — stage logs were 0 bytes for the entire run; progress events
  never reached stdout. Fixed, but not yet in a built binary, which is why this
  stall had to be diagnosed from the events file rather than the stage log.
- `15c3131f644` — the `Dict.clear()` fix that got stage 3 past the previous
  failure point and exposed this.
