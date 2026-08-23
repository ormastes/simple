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

## Update 2026-08-23 — a third defect: neutralised in-development specs were recorded as PASSED

**This section supersedes an earlier version of itself that was WRONG. The
earlier text is not preserved because it would read as a competing
explanation; what it claimed, and why it was wrong, is stated below instead.**

### What I claimed, and why it was wrong

I originally reported that in-development was being *absorbed into
`skipped`*, reasoning from the runner source: the
`InDevelopmentOutcome.ExpectedFailure` arm returns a `TestFileResult` with
`passed: 0, failed: 0, skipped: expected`, and no per-test DB status existed
to distinguish it. The inference — "so the `Skipped` row must contain them" —
was **wrong**, because it stopped at the struct and never followed the value
to the DB **write site**.

### What actually happened (measured, by the runner lane)

`update_test_database` chose the row status with `if file_result.is_ok()`.
A neutralised in-development file has `failed == 0`, so **`is_ok()` returned
true** and the row was written as **`passed`**.

Measured on the real path: `neutralised_is_ok=true in_development=2` →
after the fix, `written_status=in_development`.

### Why the corrected version is worse, not merely different

An omission is a gap; an overcount is a number that actively misleads in the
reassuring direction.

- Pre-fix DB rows **understate in-development** *and* **overstate passed**,
  by exactly the same specs.
- So **any historical DB-derived pass rate is an OVERCOUNT** — every
  `Passed` figure in a pre-fix `test_result.md`, and every `pass_rate` in a
  pre-fix `stats --json`, is inflated by the in-development population.
- This is not visible by subtraction from the report, because the totals
  still reconcile perfectly. A green-looking, self-consistent summary was
  the symptom.

### The fix, and where it lives

`TestStatus.InDevelopment` (`test_db_types.spl`), status string
`in_development`; `str_to_status` also accepts `"in-development"`. The new
check is ordered **ahead of** `is_ok()` — which is precisely why this was
unfixable from the reporting side: by the time any reporting surface saw the
row, the status was already `passed` and the evidence was gone.

The reporting surfaces here query both spellings
(`tests_by_status("in_development")` and `"in-development"`), so they begin
reporting correctly the moment a run is recorded by a runner carrying that
status, with no further change.

### The reconciliation gate is blind to this class — stated, not glossed

`check-test-summary-reconciles.shs` was added by this lane as the safety net
for exactly this family of defects. **It cannot catch this one.** Folding
in-development into `passed` moves a count between addends; the total is
unchanged, so the gate stays green.

That is worth stating plainly because the gate has been cited as the reason
these numbers can be trusted. What it actually proves is that no category
was **dropped**. It proves nothing about whether each category was
**classified correctly**, and a defect that misclassifies while preserving
the sum is invisible to it.

Found the honest way: the first draft of the regression example asserted
that the folded numbers would fail to reconcile. It failed. The assertion
was wrong, not the code.

### Related trap, one level lower — unrecognised status silently becomes Skipped

`str_to_status` ends in `case _: TestStatus.Skipped`
(`test_db_types.spl:132`). Any status string it does not recognise is
**silently relabelled a skip** — no error, no warning. Both in-development
spellings are now explicit cases, so they cannot hit it; but **a future
status added without touching that function will be silently mislabelled**,
and will look like a legitimately-skipped test. A fallback that quietly
picks a real, meaningful status is strictly worse than one that fails loudly
or maps to an explicit `Unknown`.

### Still open on the runner lane's side — do not build on it

`Results:` still shows a `skipped` count for tagged files (3 failing
examples → `3 skipped`) while `States:` reports correctly. The runner lane
has ruled out the struct, the write site and the printer, and is running an
untagged 3-failure control to establish whether that count is pre-existing
behaviour from a different lane rather than the tag path. It will be filed
as its own defect rather than folded into this one. **No surface here reads
that `Results:` skipped count.**
