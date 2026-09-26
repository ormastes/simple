# bootstrap47: stage-2 `compiler_bootstrap_tests` runner died silently; SCV prime took 766 s and reported `check rc=1`

- **Filed:** 2026-09-26
- **Status:** prime cost/rc — FIXED (prime probe is now `check --help`).
  Runner death — NOT REPRODUCED with identical binaries; open, needs lane-side
  diagnostics on the next occurrence (see "What to capture").
- **Lane:** Windows bootstrap47, `ad6c60e9256`, stage-2 compiler tests,
  delegated seed `2e0f7eb4…` (includes #1650 / #1651).

## Symptoms

1. `compiler_bootstrap_tests` FAIL after 21 s. The log ends after the first
   `[route]` / `[diag] resolved child binary` line, with no FAIL/PASS line and no
   summary. The watchdog receipt `simple-process-tree-rss.48200.env` records
   `root_exit_raw=0x1`, `abnormal_exit_ntstatus=0x0`, 102 samples (≈10 s of
   workload), peak RSS 586 MB, and `status=complete`.
2. `scv_inventory_prime`: warm admission took 766 s with `check rc=1`, and
   `scv_inventory_prime.log.warm` was empty.

## Findings

### Prime (explained, fixed)

The warm pass ran `simple_cli check src/lib/common/text_whitespace.spl`.
`check` does three things:

- It runs SCV admission before parsing arguments. That is the only part the
  prime needs.
- It semantic-checks the file. The pure-Simple checker reports 5 pre-existing
  errors on that file. The **b46 CLI reports the same 5 in the same tree**, so
  this is not new.
- It runs the repo hygiene gate: `repo_hygiene_gate.spl` →
  `process_run("sh", ["scripts/check/check-repo-hygiene.shs"])`.

Before `dac914d9306`, Windows `process_run` never started anything and reported
exit 0 (`windows_rt_process_run_always_exit_zero_2026-09-26.md`), so the gate
was a silent no-op. Now it really runs:

- Measured 155 s standalone on an idle host, and more under bootstrap load.
- On a bootstrap worktree it FAILs with 15 violations. That adds an error
  (`6 error(s) in 2 of 1 file(s)`) and gives rc=1.

Most of the 766 s is SCV snapshot materialization, not the hygiene gate. With
the lane's pre-run `build/scv` copied in, `check --help` alone took 987 s
(rc=0) on this host. The first spec child afterwards passed admission and
delegated in 14 s.

Fix: the prime probe is `check --help`.

- It is admitted exactly like a spec child. Measured: with no journal it prints
  `SCV-E-ADMISSION: compile-event-journal-missing` and returns rc=1.
- It does the same warm materialization that a file check does, as the
  987 s / 14 s measurement shows.
- With a warm journal it exits 0 in about 10 s.
- It never checks a file or runs the hygiene gate. That removes the spurious
  rc=1 and the gate's 155 s+ from every prime.

### Runner death (not reproduced)

Every run below used the lane's exact artifacts:

- stage-2 `simple_cli` / `simple_test_runner` from `6810c8ad5cfd3432/bacae05122293244`
- the rebuilt seed (sha256 `2e0f7eb4…`)
- the lane's `build/scv` state, copied
- the same env and delegation: `SIMPLE_NO_BOOTSTRAP_DELEGATE=0`, the driver =
  seed, MC/DC off, MSYS-style `HOME`/`TMPDIR`, lane-length paths
- the lane's containment wrapper: `run-process-group-timeout.shs` → watchdog →
  `bootstrap-session-exec.exe` job object
- the same runner arguments: directory target, `--parallel --max-workers=4 --json`

Results:

- The full 71-file row completes: **69 PASS / 2 FAIL**. The failures are
  `ast_native_arena` and `stage4_closure_analysis_no_prelude_range`, the two
  known seed-vs-stale specs. Receipt: `exit_status=1`, 7567 samples, summary
  and JSON printed.
- Single-file runs of `ast_native_arena_spec` with and without the wrapper
  print their FAIL line and summary normally.

Lane-side evidence points to the runner process tree being terminated from
outside with exit code 1:

- Raw exit 0x1 with no NTSTATUS. `TerminateProcess(h, 1)` is what
  `taskkill /F` and Rust `Child::kill` produce.
- All buffered stdout was lost after the last pre-spawn flush.
- The same "empty log, rc=1" shape appeared in the prime's `check` in the same
  lane.

This is circumstantial. No killer was identified, and the lane tree is
read-only to this investigation.

## What to capture on the next occurrence

- `tasklist /v` and the Windows Application event log around the failure time.
- Whether any concurrent session ran `taskkill`, `Stop-Process`, or
  `check-simple-process-inventory.ps1 -Kill` against the host.
- Rerun the row alone
  (`BOOTSTRAP_STAGE2_TEST_DELEGATE=1 … bootstrap-phase-verification.shs`)
  to separate a transient from a deterministic failure.

## Follow-up (not fixed here)

On Windows, `simple check` now pays for and fails on the repo hygiene gate on
every invocation, because the gate finally runs there. Whether `check` should
run a 150 s+ repo-wide shell gate per call is a product decision; it is
recorded here as a perf regression exposed by `dac914d9306`.
