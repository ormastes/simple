# Test runner: a preflight abort emits a `Results:` line that reads as a mass failure

- **Filed:** 2026-08-23
- **Status:** FIXED (reporting half). Watchdog truncation half OPEN, handed to the lane owning `src/app/test_runner_new/**`.
- **Severity:** High — corrupts the repo's designated evidence line.

## Symptom (measured)

`bin/simple test test/03_system/feature`:

```
ERROR: System test(s) missing required # @cover annotation:
  ...
Results: 587 total, 0 passed, 587 failed
Time:    0ms
```

~3 minutes, 3,037 lines, `[MEM] AFTER_RUN_0_files`, and **not one**
`PASS` / `FAIL` / `SPEC FILE VERDICT:` line: **zero specs executed**, rc=3.
Also measured: 51 in `test/03_system/infrastructure`.

## Why this is serious

`.claude/rules/testing.md` tells every reader that `Results:` is the
authoritative verdict. A fully-formed `Results:` line with a large `failed`
count is indistinguishable, to any automated reader, from a real mass failure.
Four sweep lanes were about to classify and tag healthy specs from it.

A missing coverage annotation is **annotation debt**, not a test failure.

## Root cause

`src/app/test_runner_new/test_runner_main.spl:268-283` (the `@cover` gate)
returns `TestRunResult(files: [], total_failed: missing_covers.len())` before
the executor starts. `print_summary`
(`src/lib/nogc_sync_mut/test_runner/test_runner_output.spl`) then renders that
struct through the ordinary aggregate path, manufacturing a completed-run
report out of a preflight abort.

## Design decision

**Invariant: a run in which zero specs executed must never produce output that
reads as a completed run with failures.**

Chosen: keep the gate strict, and make its abort **impossible to mistake for
execution** — refuse to emit `Results:` / `Time:` / any pass-fail verdict at
all, printing an `ABORTED BEFORE EXECUTION` block instead. Rejected
alternatives:

- *Report as a distinct outcome inside `Results:`* — still emits the line CI
  and agents grep, so a reader that only matches `^Results:` is still fooled.
- *Make the gate advisory by default* — fixes this one gate's blast radius but
  not the class; the next preflight gate reintroduces it. Also changes policy,
  which was not established as safe.

Detection is **structural, not gate-specific**: no per-file result exists,
nothing passed, yet a nonzero failure figure is claimed
(`run_aborted_before_execution`). Every present and future preflight abort is
covered by construction. A genuine empty selection (0 files, 0 failures) is
excluded and still prints `No tests selected.`

The fix lands entirely in `src/lib/nogc_sync_mut/test_runner/` — the printer,
the correct chokepoint — and deliberately does **not** touch
`src/app/test_runner_new/**`, which another lane is actively editing.

### `--no-cover-check` default

`--no-cover-check` already exists (`test_runner_args.spl:484`), so strict is a
choice, not a necessity. `git log -S` on the gate surfaces it only inside bulk
sync commits (`aff29a24dfe`, `78dbaff5d7c`, `cfe0506e336`) with no design
rationale recorded — i.e. no evidence the strict default was a deliberate,
reviewed decision. It is nevertheless **left unchanged**: this fix makes the
strict default safe to keep, so changing policy is unnecessary.

## Sibling abort paths (the class)

1. **`@cover` gate** — `test_runner_main.spl:268-283`. Fixed by this change.
2. **Resource self-protection watchdog** — `test_runner_main.spl:369,412`,
   `resource_limit_pct` default 75, sampled every 20 tests, exit 42
   (`EXIT_RESOURCE_SHUTDOWN`). Prints a plausible partial summary
   (`Completed tests: 20 / Passed: 106`) that reads as a completed run, so a
   sweep silently measures only the first 20 specs per directory. Bypass
   `--no-self-protect`. **Not fixed here** (owned file). Two points for the
   owner: it samples **system-wide** CPU/memory, so on a shared box it aborts
   because of *other* processes — arguably the deeper bug; it should measure
   the runner's own process tree/cgroup, or at minimum report what it measured.
   And the summary must state plainly that the run was **truncated and at which
   count**.
3. `test_runner_main.spl:230,300,304` return empty results for `--list` /
   no-op paths; those carry `total_failed: 0` and correctly read as
   "No tests selected."

`reconcile_discovered_vs_executed` (`test_runner_main.spl:895`) already covers
mid-run truncation by converting unexecuted discovered files into counted
failures — it is the precedent this fix follows, and it does not fire for
preflight aborts because discovery-vs-execution never runs.

## Annotation debt

Tree-wide population, measured 2026-08-23 with the runner's own predicate
(`test/**` `*_spec.spl` under `/system/` or `/03_system/`, excluding
`/helpers/` and `/fixtures/`, `# @cover` in the first 30 lines):

- **5,370** system specs total
- **3,153** annotated
- **2,217 missing `# @cover`** (41%)

Top directories: `test/03_system/feature` 543, `tools` 408, `app` 273,
`check` 163, `os` 161, `gui` 97, `test/system/app` 95.

**Recommendation:** do **not** bulk-add annotations, and do **not** tag these
specs as in-development — a sibling lane established this is harness debt, not
unfinished feature work. Burn it down per-directory by the owning lane as part
of normal work. Until then `--no-cover-check` is the correct invocation for
sweeps; with this fix, a run that forgets it can no longer be misread.

## Reproduce

`test/01_unit/lib/test_runner/zero_executed_abort_no_results_line_spec.spl`
(RED before the fix: `run_aborted_before_execution` did not exist and the abort
shape rendered a `Results:` line).

## For the sweep lanes

Nothing changes about how to invoke: keep passing `--no-cover-check`. What
changes is how to READ a run — if you see `ABORTED BEFORE EXECUTION`, the
counts are **UNKNOWN**, not failures, and must not be used to classify specs.
