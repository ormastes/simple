# Test DB is incoherent: totals do not reconcile, and the file→name join is wrong

- **Filed:** 2026-08-23
- **Status:** OPEN
- **Surfaces:** `doc/08_tracking/test/test_result.md`, `doc/08_tracking/test/test_db.sdn`,
  `src/lib/nogc_sync_mut/test_runner/{doc_generator.spl,test_db_io.spl,test_db_parser.spl}`
- **Gate:** `scripts/check/check-test-summary-reconciles.shs` (ADVISORY — honestly RED, see below)

## Symptom

Two independent defects in the same recorded artefacts.

**1. Totals do not reconcile.** `doc/08_tracking/test/test_result.md` reads
**Total 770 / Passed 0 / Failed 0**. A tracker that knows about 770 tests and
holds a verdict for none of them is broken, not green — but it was published
as a report, and `bin/simple stats` read `| Total |` and `| Passed |` straight
out of it and printed a 0% pass rate as if that were a measurement.

**2. The `tests → suites → files` join is wrong.** `test_db.sdn` holds **74
counter rows for 770 tests**, and the joins disagree: file
`qemu_user_integration_spec.spl` is paired with name
`runtime_array_assignment_ssa_spec.spl`. Per-test attribution in the DB
therefore cannot be trusted at all — not the pass/fail of any individual
test, and not any per-file or per-suite rollup derived from it.

## Why every existing guard was green over this

All the pre-push guards check trees, ranges, or source: conflict entries,
marker text, file counts, test-tree diffs, blob-vs-history, `rt_*` symbol
sets, C that parses, stage binaries that run. **None of them ever reads the
numbers in the report.** A summary table that is well-formed Markdown,
correctly sized, non-conflicted and forward-moving passes all of them while
being arithmetically impossible.

## Impact on the in-development reporting lane

This was found while adding an in-development category to the statistics
surfaces. Adding a count to a summary that already reports `Passed 0 of 770`
would be building on sand, so:

- The **reconciliation assertion is now a GATE**, not just a spec assertion:
  `scripts/check/check-test-summary-reconciles.shs`. Its selftest is fatal (4
  fixtures, incl. a replay of the exact 770/0/0 shape, which must FAIL).
  Against the real `test_result.md` it reports
  `FAIL — 7 metric(s) checked: 770 test(s) recorded, 0 with a verdict.`
  It lands **ADVISORY** for that reason; promote it to a blocking push row in
  `config/check/must_check_gates.sdn` once a real run makes it green.
- `generate_test_result_md` now emits an `| Other |` row for any unaccounted
  remainder, so the same class becomes self-describing in the artefact rather
  than needing someone to do the subtraction.
- **Stated plainly: the in-development counts sourced from this DB are only
  as trustworthy as the DB, which is currently not trustworthy at all.** The
  tag-index counts (`bin/simple tags`) are independent of it — they are read
  from source annotations — and are the trustworthy number today.

## Repro

```sh
grep -E '^\| (Total|Passed|Failed) \|' doc/08_tracking/test/test_result.md
sh scripts/check/check-test-summary-reconciles.shs   # FAIL, exit 1
```

## Not yet root-caused

Whether the 74-rows-for-770-tests discrepancy and the file→name mispairing
share a cause (one bad index/offset in the V3 SDN table parse at
`test_db_parser.spl:92`, which would explain both a short row count and a
skewed column association) or are two defects is **not established** and must
not be assumed. Both need to be reproduced against a freshly written DB
before anything is changed.

## Update 2026-08-23 — a third defect: in-development is absorbed into `skipped`

Found while wiring the three-state reporting surfaces.

`src/app/test_runner_new/test_runner_main.spl` neutralises an in-development
file by returning a `TestFileResult` with `passed: 0, failed: 0, skipped:
expected` (the `InDevelopmentOutcome.ExpectedFailure` arm). The count is
therefore stored **in the `skipped` field**, and **no per-test DB status
distinguishes an in-development file from a genuine host-unavailable skip.**

Consequences for the reporting surfaces:

- `db.tests_by_status("in_development")` can never match anything, so
  `test_result.md`'s `| In Development |` row is **structurally 0** — not
  measured, and not a real zero.
- The `| Skipped (host-unavailable) |` row **silently contains** the
  in-development files, which is exactly the "absorbed into skipped" hole the
  category was created to close.

This is not something the reporting lane can fix from its own side: it needs
either a per-test status recorded by the runner, or a distinct field on
`TestFileResult`. Both belong to the runner lane. Until then:

- `test_result.md` prints an explicit caveat under the summary whenever the
  in-development count is 0, rather than publishing a confident zero.
- **`bin/simple tags --tag in-development` is the real number.** It is
  source-derived (read from `@tag:` annotations) and independent of the DB.

The runner-side classification itself is correct and was NOT the problem —
`classify_in_development` distinguishes ExpectedFailure / UnexpectedPass /
LoadFailure properly. The loss happens at the point the outcome is written
back into a `TestFileResult` that has no field to hold it.
