# The `# @cover` gate marks 227 system tests FAILED without running a single one

**Status:** OPEN
**Found:** 2026-08-04
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
