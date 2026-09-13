# doc_coverage csv_exporter: undefined `NL` import + DocItem missing create_class/create_enum
- Status: RESOLVED (2026-09-12) — see Triage 2026-09-12; csv 28/28 and json 26/26 green in both the live and legacy test trees

## Symptom

`test/01_unit/app/doc_coverage/csv_export_spec.spl` fails all 28 examples with:

```
semantic: variable `NL` not found
```

and 2 of those 28 additionally show (once the `NL` blocker is worked around mentally):

```
semantic: unknown static method create_class on class DocItem
semantic: unknown static method create_enum on class DocItem
```

Sibling spec `test/01_unit/app/doc_coverage/json_export_spec.spl` fails with the same
family of "Cannot resolve module" symptom at the import-path layer (see below), and is
likely to hit the same or a similar downstream issue once its import path is corrected.

## Root cause 1 (test-file layer, already fixed in this file)

`test/01_unit/app/doc_coverage/csv_export_spec.spl` imported via:

```
use doc_coverage.reporting.csv_exporter.{export_coverage_csv}
use doc_coverage.types.doc_item.{DocItem, DocKind}
```

which fails module resolution (`error: semantic: Cannot resolve module:
doc_coverage.reporting.csv_exporter`) from a `test/` caller, even though the module
exists at `src/app/doc_coverage/reporting/csv_exporter.spl` and is imported
successfully *without* the `app.` prefix from sibling files inside `src/app/**`
itself (e.g. `src/app/doc_coverage/reporting/csv_exporter.spl` imports
`doc_coverage.types.doc_item.{DocItem}` with no prefix and that resolves fine at
the source layer). From `test/`, the working convention (matching
`test/01_unit/app/doc_coverage/compiler_integration_spec.spl`) requires the
`app.` prefix. This part was fixed here (value-preserving import path edit only):

```
use app.doc_coverage.reporting.csv_exporter.{export_coverage_csv}
use app.doc_coverage.types.doc_item.{DocItem, DocKind}
```

`json_export_spec.spl` has the identical un-prefixed pattern
(`use doc_coverage.reporting.json_exporter...`) and fails identically; it was left
untouched (out of shard scope) but the same one-line prefix fix likely applies.

## Root cause 2 (genuine source bug, NOT fixed — out of test-shard scope)

After the import-path fix, `src/app/doc_coverage/reporting/csv_exporter.spl` itself
fails to compile:

```spl
# src/app/doc_coverage/reporting/csv_exporter.spl
use doc_coverage.types.doc_item.{DocItem}
use std.string.{NL}                                    # <-- NL not exported by std.string

fn export_coverage_csv(items: [DocItem]) -> text:
    var csv = "name,file,line,kind,is_public,has_sdoctest,has_inline_comment,tags{NL}"
    ...
        csv = "{csv}{row}{NL}"
```

`std.string` (`src/lib/string.spl`) does not define/export an `NL` constant — grep
over `src/lib/string.spl` and `src/lib/common/` finds no `NL` definition. Every
example in the spec constructs a CSV string via `export_coverage_csv`, so every
example trips this same "variable `NL` not found" semantic error.

## Root cause 3 (genuine test/source mismatch, NOT fixed)

`test/01_unit/app/doc_coverage/csv_export_spec.spl` lines 248 and 256 call:

```spl
val item = DocItem.create_class("MyClass", "/src/std/test.spl", 10, 5, "pub")
val item = DocItem.create_enum("Status", "/src/std/test.spl", 10, 5, "pub")
```

but `src/app/doc_coverage/types/doc_item.spl` only defines `create_function` (line
25) and `create_struct` (line 42) as static constructors — no `create_class` or
`create_enum`. These are real missing API surface, not a naming/rename issue (no
`create_class`/`create_enum`-shaped function exists anywhere else in that file to
rename to).

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/app/doc_coverage/csv_export_spec.spl --no-session-daemon
```

## Fix hypothesis (not attempted — src/** out of test-shard scope)

1. Add a `NL` (or equivalent) newline constant export to `std.string`
   (`src/lib/string.spl`), or change `csv_exporter.spl` to use a literal `"\n"` /
   existing newline helper instead of importing a nonexistent `NL`.
2. Either add `DocItem.create_class` / `DocItem.create_enum` static constructors
   (mirroring `create_function`/`create_struct`), or remove/rewrite the two
   related `it` blocks in the spec once the correct API is confirmed with the
   doc_coverage module owner (do NOT silently delete — file/confirm first).

## Affected specs

- `test/01_unit/app/doc_coverage/csv_export_spec.spl` (in shard, import path fixed,
  still failing on root causes 2 and 3 above)
- `test/01_unit/app/doc_coverage/json_export_spec.spl` (same import-path symptom,
  not in shard, untouched)

## Triage 2026-09-12
Rule B: ran `bin/simple test test/01_unit/app/doc_coverage/json_export_spec.spl` on the deployed seed; it FAILs, confirming the defect still reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Triage 2026-09-12

Binary: `bin/simple` = shared clone's Rust seed, `sha256 3d120a6f…`, aarch64.

RED at the start of this session — both exporters' specs, live and legacy:

```
test/01_unit/app/doc_coverage/json_export_spec.spl  declared>=26 executed=0  (Cannot resolve module: doc_coverage.reporting.json_exporter)
test/01_unit/app/doc_coverage/csv_export_spec.spl   declared>=28 executed=28 passed=0 failed=28 (variable `NL` not found)
```

`create_class` / `create_enum` (root cause 3 in this record) already exist, so
that half was fixed upstream. Five defects remained, every one of them in
**product** source rather than in a spec — the two exporters had drifted away
from the types they read and nothing exercised them:

1. `reporting/{csv,json,terminal}_exporter|renderer.spl` imported `NL` from
   `std.string`, which does not export it. Now `std.common.text`
   (`src/lib/common/text.spl:3`, the only definition, and it is exported).
2. `csv_exporter.spl:26` read `item.file`; the field is `file_path`.
3. `json_exporter.spl:59` read `file_cov.file_path`; the field is `path`.
   (The two exporters had the same mistake in opposite directions.)
4. `CoverageReport.overall_percent()` / `.sdoctest_percent()` and
   `FileCoverage.coverage_percent()` / `.sdoctest_percent()` were called by
   `json_exporter.spl` and declared nowhere. Added, with zero items defined as
   100% — a report with nothing in it has nothing missing — rather than a
   division by zero.
5. `DocItem.sdoctest_tags` was read by `csv_exporter.spl:34` and declared
   nowhere. Added as `[text] = []` so the four `create_*` constructors are
   untouched.

The spec-side import prefix (root cause 1) was still wrong in the json and csv
specs in both trees (`doc_coverage.*` -> `app.doc_coverage.*`, the convention
the record already identified).

GREEN:

```
test/01_unit/app/doc_coverage/csv_export_spec.spl   outcome=OK executed=28 passed=28
test/01_unit/app/doc_coverage/json_export_spec.spl  outcome=OK executed=26 passed=26
test/unit/app/doc_coverage/csv_export_spec.spl      outcome=OK executed=28 passed=28
test/unit/app/doc_coverage/json_export_spec.spl     outcome=OK executed=26 passed=26
```

Whole directory re-run before/after: no verdict line moved backwards.
`markdown_report_spec` 29/29, `threshold_system_spec` 17/17,
`compiler_integration_spec` 8/8, `group_comment_detection_spec` 30/30 all still
green. The directory's other reds (`tag_generator`, `tag_validator`,
`threshold_calculator`, `threshold_parser`, `init_parser` — all `executed=0`,
plus `sdoctest_coverage` 0/6 and `analysis_exports_defined` 2/3) are untouched
pre-existing failures in unrelated modules.
