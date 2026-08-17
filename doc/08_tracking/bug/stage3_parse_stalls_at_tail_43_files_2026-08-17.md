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

## UPDATE — the run ended in an external SIGTERM, not a stall resolution

At elapsed ~26 min the run ended:

```
warning: stage3 self-host failed (exit 143); Stage 4 unavailable
Stage 3 unavailable — no provenance-verified compiler for Stage 4
```

**Exit 143 = 128+15 = SIGTERM.** Per `.claude/rules/testing.md`, `rc=143` with no
result line means **UNVERIFIED, not failed**. So this run proves neither that the
stall would have resolved nor that stage 3 is broken. The stall measurement above
(547s at done=576) stands on its own; the ending does not.

### The sender is NOT identified. Candidates checked and their status:

- **`timeout`/`run_timeout` in the bootstrap script — RULED OUT.** `run_timeout`
  and `run_timeout_kill` exist (lines 691, 703) and `timeout` does send SIGTERM,
  which would produce exactly 143. But no caller wraps the stage-3 native-build:
  every call site is a 10/30/60/180s smoke or gate (lines 1004, 1007, 2300, 2409,
  2418, 2429, 2432, 2582, 2635, 2651). None is stage 3.
- **`kill-simple-monitor.service` — NOT MATCHED by its own thresholds.** The unit
  is `active` and `enabled`, respawning every ~15s (restart counter **429**), and
  it is NOT logging kills. But its guards are `KILL_SIMPLE_MEM_MB=24000` (we
  measured 8.0 GB) and `KILL_SIMPLE_CPU_PCT=95` with a consecutive-poll
  requirement (we measured 75-83% of ONE core). It also targets `bin/simple
  run|test`; the stage-3 process is `simple native-build`. On the recorded
  numbers it should not have fired. **Not exonerated** — it is unlogged, so
  absence of evidence is not evidence of absence — but not demonstrated either.
  Note `KILL_SIMPLE_MIN_AGE_SECS=7200` was exported for the bootstrap, which does
  NOT reach the systemd unit: it has its own environment.
- **Another session/agent.** ~13 peer sessions and ~190 claude processes were
  live. Unproven.

### Why this matters more than the stall

A single external SIGTERM discards a 26-minute build and every diagnostic in it.
This is the same evidence-corruption class already recorded for specs, where a
SIGTERMed run "launders through a pipe as exit 0 with no Results line". The
durable fix is the one now being built: per-file process isolation with a
supervisor, so a death — of a worker OR of the parent's child — is recorded
against a named file and the remaining files still compile.

**Do not re-run and hope.** Before the next attempt, either identify the sender
or run the stage under a recorded wrapper that captures who signals it
(e.g. keep the parent's `wait` status and log the signal number per child).
cat >> "$D" <<'EOF'

## RETRACTION (2026-08-17, later the same day)

**The central claim of this document — that stage-3 parse stalled for >547s on
its last 43 files — is FALSE.** Stage 3's native-build ran to COMPLETION and
returned nonzero. Parse finished.

Evidence, from the failing run's own artifacts:

- `stage3-sanity.env` — the evidence path handed to `bootstrap_stage_sanity`
  (`scripts/bootstrap/bootstrap-from-scratch.sh:1572`) — **does not exist**, so
  the sanity branch at `:2062` was never entered.
- `runtime-after-stage3.txt` **exists, mtime 08:28**, matching the 08:29 exit.
  It is written at `:2050-2052`, i.e. **after** the native-build returned and
  **after** the admitted-stage2 and frozen-runtime provenance checks passed.

So: parse completed, the build completed, provenance was clean, and the compiler
exited nonzero for some other reason. The `done=576 remaining=43` sample was
simply the last receipt written before the phase advanced — precisely the
staleness artifact that `4d1aca2d799` (per-file reporting) removes. Every
measurement in the body above is real; the INFERENCE drawn from it was not.

`src/std/nogc_sync_mut/sffi/dynamic.spl` is also empirically cleared: it lexes in
**161 ms** (8,497 bytes), six orders of magnitude short of 550s.

### What survives, and is the real defect

**A stage-3 compile failure is currently UNATTRIBUTABLE.**
`stage3-native-build.log` is 0 bytes after a 26-minute failing run. The redirect
itself is correct (`) >"$log" 2>&1` at
`scripts/check/lib/bootstrap-stage3/command-snapshot.shs:227`, with rc read on
the next line at `:228`). The log is empty because the in-process pure-Simple
driver is **silent on success** and routes diagnostics only to
`SIMPLE_BUILD_PROGRESS_EVENTS` (`driver_log_helpers.spl:112,156`).

That silence is load-bearing for a provenance gate: `bootstrap-from-scratch.sh:2114-2125`
proves the Rust seed did NOT build stage 3 by grepping the log for
`^Build complete: [0-9]+ compiled` or `^Linked: .* via clang`, which only
`native_all/src/lib.rs` emits. **Important: that gate tests for the ABSENCE OF
THOSE TWO MARKERS, not for an empty file.** So adding diagnostics is safe as long
as no line begins with those markers — verified for the `[build] ...` lines added
by `b4872f73454`, which match neither pattern.

This is why three separate lanes guessed at this failure: there was no trail.

### Corrected next steps

1. Get the actual stage-3 failure text. `b4872f73454` (progress to stdout) plus
   `4d1aca2d799` (per-file receipts) should make the next run attributable —
   confirm the running stage-2 binary carries both before trusting its receipts.
2. Do NOT chase a parse stall. Retired as non-causes: `hir_lowering_quadratic_symbol_define_2026-07-28`
   (fixed at `027666759ff`, and the wrong phase), and
   `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20` (its signature is
   memory GROWTH; RSS here was flat at ~51 KB/s).
3. The superlinear-cost link to `lint_timeout_hwir_zca_rows_2026-08-17` remains an
   open, unproven hypothesis — but it is no longer supported by this run.

### Process note worth keeping

This document was filed with a confident causal title on top of correct
measurements. The measurements were fine; the inference was not, because a
progress counter that only reports every 64 files was read as a position. A
stale field is not evidence of a stall. Prefer "last observed receipt was X"
over "it is stuck at X" unless the process's own artifacts corroborate it.
