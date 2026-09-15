# Test DB is incoherent: totals do not reconcile, and the file→name join is wrong

- **Filed:** 2026-08-23
- **Status:** FIXED 2026-09-14 (reconstructed V3 snapshot; malformed-load rejection added)
- **Surfaces:** `doc/08_tracking/test/test_result.md`, `doc/08_tracking/test/test_db.sdn`,
  `src/lib/nogc_sync_mut/test_runner/{doc_generator.spl,test_db_io.spl,test_db_parser.spl}`
- **Gate:** `scripts/check/check-test-summary-reconciles.shs` (ADVISORY — honestly RED, see below)

## Symptom

Two independent defects in the same recorded artefacts.

## Resolution (2026-09-14)

The committed file was a concatenation of parallel legacy snapshots, not one
database: primary IDs restarted, only 73 strings survived while references
reached 862, and its eight-field test rows did not match the V3 schema.  The V3
snapshot was reconstructed from the 859 unique status rows in `test_result.md`:
63 passed, 42 failed, and 754 explicitly `unknown`.  No unknown result was
promoted to passed.  Unattributable aggregate timing/run data was omitted from
the new empty V3 volatile database; the corrupt input remains recoverable from
Git history at `8bc9a7923d7`.

The production parser now reports an integrity error for non-contiguous primary
IDs, legacy-width test rows, missing strings, and missing file/suite references;
`RunnerTestDbCore.load` and `load_from` reject such data before rebuilding
indexes or saving it back.

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
