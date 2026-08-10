# The `# @cover` gate reports 791 un-annotated legacy feature specs as test FAILURES

**Status:** OPEN (re-verified 2026-08-10, architectural — root cause unchanged)
**Found:** 2026-08-04
**Severity:** high · **Area:** test runner / legacy feature suite
**Found during:** legacy-feature-test triage (`test/03_system/feature/**`)

## Symptom

Running any `test/03_system/feature/**` subdirectory reports every spec in it as
a *failed test* without executing a single example:

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/03_system/feature/language
ERROR: System test(s) missing required # @cover annotation:
  test/03_system/feature/language/async_default_spec.spl
  ... (16 files)
Found 16 system test(s) without # @cover.
Results: 16 total, 0 passed, 16 failed
```

Actual: `16 total, 0 passed, 16 failed`, nothing executed.
Expected: either the tests run, or the policy violation is reported as a *lint /
gate* verdict that is not counted in the `Results:` line as failed tests.

With the gate bypassed the same directory is almost entirely green:

```
$ ... bin/simple test test/03_system/feature/language --no-cover-check
Results: 261 total, 256 passed, 5 failed
```

So the reported "failure" count for the legacy feature tree is dominated by a
missing annotation, not by broken behaviour.

## Root cause

Two separate things, both proved:

1. **The tests are the stale side of the policy.** The policy is intentional and
   documented — `doc/07_guide/infra/testing/coverage.md:337`: *"Canonical
   `test/03_system/**` specs require at least one annotation unless
   `--no-cover-check` is explicitly selected."* The legacy feature specs predate
   it. Measured 2026-08-04 (non-helper `*_spec.spl` / `*_test.spl`):

   | tree | files | with `# @cover` | missing |
   |------|-------|-----------------|---------|
   | `test/03_system/**` | 3893 | 1758 | 2135 |
   | `test/03_system/feature/**` | 1046 | 255 | **791** |

2. **The gate mis-reports itself as test failures and aborts the whole run.**
   `src/lib/nogc_sync_mut/test_runner/test_runner_main.spl:155-168` returns
   `TestRunResult(files: [], total_passed: 0, total_failed: missing_covers.len(), ...)`
   and returns immediately. Consequences:
   - a policy violation is indistinguishable from a real assertion failure in
     the authoritative `Results:` line;
   - **one** un-annotated file suppresses execution of every *annotated* spec in
     the same directory, so specs that do satisfy the policy never run either.
   The predicate itself is
   `validate_system_test_covers` at
   `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:151-162`.
   The same pair exists in the second entrypoint,
   `src/app/test_runner_new/test_runner_main.spl`.

## Why not fixed now

Item 1 needs 791 *truthful, per-spec* `# @cover <src path> <pct>` annotations.
The target file and percentage are a per-spec judgement — existing annotations
are specific (e.g. `# @cover src/lib/common/math_repr.spl 90%`), and under
`--coverage` a wrong path or an unmet percentage *fails the run*
(`check_cover_annotation_thresholds`, `test_runner_main.spl:834`). Bulk-adding a
generic annotation would fabricate a coverage claim and convert this gate
failure into a coverage failure — strictly worse. It needs a per-directory
migration pass, one owner module at a time.

Item 2 is a small runner change (report the gate as its own verdict rather than
as `total_failed`, and let annotated files still run), but it changes the
meaning of the `Results:` line that other lanes and CI parse, so it should land
deliberately and not as a side effect of a test-triage session.

## Workaround

`--no-cover-check` gives the real behavioural verdict for the legacy tree.

## 2026-08-10 re-verification

Re-read `src/lib/nogc_sync_mut/test_runner/test_runner_main.spl:154-168` —
the early `return TestRunResult(files: [], total_passed: 0,
total_failed: missing_covers.len(), ...)` on a non-empty `missing_covers`
list is byte-for-byte unchanged from the original report. Root cause and
scope assessment both still hold:

- Item 1 (791 missing `# @cover` annotations) is a per-spec, per-owner-module
  content migration, not a code fix — out of scope for a single session.
- Item 2 (gate mis-reported as `total_failed`, aborting the whole directory)
  is a real, fixable defect, but the fix changes the meaning of the
  `Results:` line that other lanes/CI parse as the authoritative verdict
  (`testing.md` "Results line is authoritative" rule). Landing it requires
  auditing every consumer of that line first; doing so as a drive-by inside
  an unrelated 4-doc sweep in a shared working copy risks a silent,
  wide-blast-radius change to CI semantics. Left OPEN and
  architectural/deferred, not silently downgraded.

No code changed for this doc; only this confirmation note.
