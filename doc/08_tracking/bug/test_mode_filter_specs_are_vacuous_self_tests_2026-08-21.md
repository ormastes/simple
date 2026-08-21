# Test mode-filter specs are vacuous self-tests, and the skip marker they assert on is corrupted

Status: RESOLVED (2026-08-21)
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

## RESOLVED 2026-08-21 — option (yes): mode filtering implemented as product code

The product decision was taken as **yes**: per-file mode filtering now exists,
the specs import it, and the corrupted marker is repaired to its real spelling.

- **New module** `src/lib/nogc_sync_mut/test_runner/mode_filter.spl`:
  `extract_directive_lines`, `extract_mode_tags`, `file_get_mode_tags`,
  `file_mode_matches`, `content_mode_matches`, `path_mode_matches`. Exported
  from `src/lib/nogc_sync_mut/test_runner/__init__.spl`. `bin/simple lint` clean.
- **Marker restored.** The corrupted `# skip-marker-removed_mode:` is now
  `# @skip_mode:` everywhere (6 files). The corrupted spelling was 27 chars
  while the specs sliced `[13:]` — `# @skip_mode:` is exactly 13, which
  confirms the original spelling arithmetically. The specs were in fact RED on
  it (`mode_filter_spec` was 14 total, 11 passed, 3 failed), not green.
- **`extract_tags` gap closed.** `tag_parsing_spec` asserts the `# @tag:` /
  `@tag:` directive form; the product
  (`test_manifest_scanner.spl:203`) only honoured `tag: "x"`. Directive support
  (bracket/quote stripping, dedupe, docstring lines) was added there.
- **Specs rewritten to import the product**, local helpers deleted, both
  `test/01_unit/` and `test/unit/` mirrors updated:
  - `test/01_unit/test_runner/mode_filter_spec.spl` — `14 total, 14 passed, 0 failed`
  - `test/01_unit/test_runner/tag_parsing_spec.spl` — `18 total, 18 passed, 0 failed`
- **Runner wiring.** `run_single_test`
  (`src/app/test_runner_new/test_runner_main.spl:706-717`) now consults
  `path_mode_matches` before dispatching to an execution mode and returns a
  skipped `TestFileResult` when the active mode is excluded — modelled on the
  adjacent `is_skip_marker_file` branch.

### Remaining, stated honestly
Enforcement could not be observed end-to-end on this host: a probe spec carrying
`# @mode: native` still executed under `bin/simple test` (interpreter). That is
because `bin/simple` is the **Rust seed**, whose own runner does not go through
`src/app/test_runner_new/test_runner_main.spl`. The Simple-side wiring is in
place; confirming it fires needs a deployed full-CLI pure-Simple binary. The
helpers themselves are proven by the two specs above against real product code.
