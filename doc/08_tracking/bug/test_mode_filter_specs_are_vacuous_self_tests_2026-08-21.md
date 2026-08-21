# Test mode-filter specs are vacuous self-tests, and the skip marker they assert on is corrupted

Status: OPEN
Found: 2026-08-21
Area: `test/01_unit/test_runner/`, `test/feature/mode_filter/`

## Symptom

`test/01_unit/test_runner/mode_filter_spec.spl` and
`test/01_unit/test_runner/tag_parsing_spec.spl` are green and assert nothing
about the product.

## Evidence

1. **No imports.** `grep -n '^use ' test/01_unit/test_runner/mode_filter_spec.spl`
   returns **nothing**. The spec imports no module at all.
2. **Helpers are local.** It defines its own
   `_extract_mode_tags` (line 6), `_file_mode_matches` (line 30),
   `_file_get_mode_tags` (line 58) and tests those.
3. **No production implementation exists.** A repo-wide
   `grep -rn "extract_mode_tags\|file_mode_matches\|mode_matches" --include=*.spl src/`
   returns only three unrelated `db_query_mode_matches_workload` hits in
   `src/lib/nogc_sync_mut/database/query_offload.spl`. There is no test
   mode-filtering implementation in `src/` for these specs to be testing.

So the specs exercise a private reimplementation that ships nowhere. They
cannot fail when the product changes, because they are not connected to it.

## Second, compounding defect: the marker string is corrupted

The specs assert on the literal `# skip-marker-removed_mode:` — e.g.
`mode_filter_spec.spl:95`:

```
val content = "# skip-marker-removed_mode: native\ndescribe \"foo\":\n..."
expect(_extract_mode_tags(content)).to_equal("!native")
```

`skip-marker-removed_mode:` is not a directive anything honours. It appears
**22 times across 6 files**, including
`test/feature/mode_filter/skip_native_spec.spl`, whose own doc comment says it
"skips native compilation via `skip-marker-removed_mode: native`". That spec is
therefore **inert** — documented as skipping native, actually skipping nothing.

Because the corrupted spelling was written into both the local helper and the
assertions, the specs remain green on the corrupted string. That self-consistency
is why this survived.

Affected files:
- `test/feature/mode_filter/skip_native_spec.spl`
- `test/03_system/feature/mode_filter/skip_native_spec.spl`
- `test/01_unit/test_runner/mode_filter_spec.spl` (+ `test/unit/` mirror)
- `test/01_unit/test_runner/tag_parsing_spec.spl` (+ `test/unit/` mirror)

Likely introduced by a bulk marker-stripping edit during the tree
wipe/restore sequence around `6f86ff32a7d` / `ae55a746719`
(`git log -S "skip-marker-removed" -- test/`).

## Why this is not fixed here

Repairing the string alone would make the specs assert a correct-looking marker
that still no reader honours, which is worse: it would *look* wired. The real
question is a product decision — should the test runner support per-file mode
filtering (`# @mode:` / `# skip_mode:`) at all?

- If **yes**: implement it in the runner, export the helpers, and rewrite these
  specs to import them instead of redefining them.
- If **no**: delete the local helpers and the specs, and remove the inert
  markers from `skip_native_spec.spl` rather than leaving them as documentation
  of a feature that does not exist.

Per repo rules the specs are **not** deleted to improve numbers pending that
decision.

## Related

- `doc/09_report/skipped_flaky_test_census_2026-08-21.md` §3a, §3b
- The adjacent, separately-fixed unanchored `# @skip` substring bug:
  `doc/08_tracking/bug/test_runner_unanchored_skip_substring_2026-08-21.md`
