# The `# @cover` gate marks 227 system tests FAILED without running a single one

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
decision needed, not a code bug
**Found:** 2026-08-04

## 2026-08-10 re-verification

`validate_system_test_covers` still lives at
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:203` (line moved
slightly since 2026-08-04) and still gates by path predicate. Re-measured the
gap directly (`/usr/bin/grep -rL '# @cover' test/03_system/ --include='*.spl'`
vs. total `*.spl` count under `test/03_system/`): **2,326 of 4,115** files
under `test/03_system/` currently have no `# @cover` line anywhere in them
(a cruder whole-file grep than the doc's original first-30-lines measure, so
not directly comparable number-for-number, but confirms the same order of
magnitude and that the annotation gap has not closed — if anything the
corpus has grown since 2026-08-04's 2,122/3,879). The gate itself is
unchanged and still fails closed with zero examples executed, exactly as
described.

This remains a rollout/policy decision (dated exemption list vs. a measured
annotation pass with coverage collection on), not something a bug-triage
session can resolve unilaterally without either fabricating coverage claims
across thousands of files or weakening a gate the repo rules explicitly
forbid weakening. Left open, consistent with the original report.
**Severity:** high — `test/03_system/app` reports 227 failures that are not test
results, and the same gate covers 2,122 specs repo-wide

## Symptom

```sh
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/03_system/app
```

Actual, verbatim tail:

```
Add at the top of each file:
  # @cover src/path/to/component.spl 80%

Bypass: --no-cover-check
Found 227 system test(s) without # @cover.
[MEM] AFTER_RUN_0_files: MemAvailable:   89169828 kB

=========================================
Results: 227 total, 0 passed, 227 failed
Time:    0ms
=========================================
```

`Time: 0ms` and `AFTER_RUN_0_files` are the tell: **no example executed.** The
227 "failures" are one policy verdict rendered 227 times, so any real pass or
failure in that directory is invisible. Re-running the same directory with
`--no-cover-check` does execute the specs (browser feature specs came back with
genuine per-example verdicts), which confirms the gate — not the specs — is what
produces the 227.

## Root cause

`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:151-162`
(`validate_system_test_covers`) collects every selected file whose path contains
`/system/` or `/03_system/`, skipping only `/helpers/` and `/fixtures/`, and
returns those with no `# @cover` in their first 30 lines
(`extract_cover_annotations_for_coverage`,
`src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl:579-591`).
`src/app/test_runner_new/test_runner_main.spl:190-203` then aborts the whole run
and reports each collected file as failed.

The gate itself is behaving as written — the annotations really are absent:

| Scope | specs | missing `# @cover` |
|---|---|---|
| `test/03_system/` | 3,879 | **2,122** |
| `test/03_system/app/` | 252 | **236** |

So the policy is far ahead of the corpus: 55% of the system suite has never
carried the annotation the runner now requires.

## Why not fixed now

Neither available move is safe from this lane:

- **Weakening the gate** (defaulting `--no-cover-check` on, or narrowing the
  path predicate) is exactly the cover-up the repo rules forbid; it would hide a
  real coverage-policy gap behind a green suite.
- **Adding 236 annotations** is not mechanical. `# @cover <path> <pct>%` is not a
  label — `check_cover_annotation_threshold`
  (`test_runner_coverage.spl:593-617`) enforces the percentage against measured
  decision coverage and fails with `@cover FAILURE: … < threshold%`, or with
  `no coverage data for <target>` when the named source is not actually
  exercised. Writing a target path and a number that were never measured would
  fabricate a coverage claim in 236 files at once.

The correct fix is a decision about the rollout — either a dated exemption list
that names the 2,122 legacy files explicitly, or a measured annotation pass done
with coverage collection on. Until then, treat the 227 in
`test/03_system/app` as **unmeasured**, not as 227 defects: the only honest
current number for that directory comes from a `--no-cover-check` run.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**STILL-OPEN, confirmed by CONTENT.**
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:203-214`
(`validate_system_test_covers`) still gates purely on the `/system/` and
`/03_system/` path substrings and flags any file whose `extract_cover_annotations`
returns empty — no test is executed to reach that verdict. Note checked and
DISMISSED during this pass: `missing.push(f)` at :213 discards its result, which
would be a silent no-op if `push` were pure — but every other call site in this
file (:115, :229, :342, :482, :523, :551, :593, :638, :720) uses the same bare
mutating form, so that is the file-wide convention, not a defect. The gate is live.
Policy decision (should a missing `# @cover` be a FAILURE or a warning?) is not a
unilateral stdlib change; left open.
