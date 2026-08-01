# doc_coverage sdoctest analysis and types modules missing

Date: 2026-05-30
Status: Resolved 2026-05-30
Severity: High

## Symptom

`test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl` fails with:

```
Cannot resolve module: app.doc_coverage.analysis.sdoctest_coverage
```

The test also imports `app.doc_coverage.types.doc_item.{DocItem, DocKind}`.
Neither module exists anywhere in `src/app/`.

## Evidence

- `find src/app -path '*doc_coverage*'` returns nothing (only `src/app/stats/doc_coverage_dynamic.spl` which is an unrelated CLI handler).
- `grep -rn 'fn validate_tag_format' src/` — no results.
- `grep -rn 'fn suggest_missing_tags' src/` — no results.
- `grep -rn 'fn match_functions_to_sdoctest' src/` — no results.
- `grep -rn 'fn extract_function_names_from_code' src/` — no results.
- `grep -rn 'enum DocKind' src/ --include='*.spl'` — no results.

## Required modules and symbols

The test expects:
- `app.doc_coverage.analysis.sdoctest_coverage` exporting:
  - `fn validate_tag_format(tag: text) -> bool`
  - `fn suggest_missing_tags(path: text) -> [text]`
  - `fn extract_function_names_from_code(code: text) -> [text]`
  - `fn match_functions_to_sdoctest(public_funcs: [text], blocks: [text]) -> ([text], [text])`
- `app.doc_coverage.types.doc_item` exporting:
  - `struct DocItem` (with `create_function(name, path, line, col, vis, sig)` constructor)
  - `enum DocKind`

## Expected

`src/app/doc_coverage/` directory with `analysis/sdoctest_coverage.spl` and `types/doc_item.spl` implementing the above symbols.

## Next Probe

Implement the missing modules under `src/app/doc_coverage/analysis/` and `src/app/doc_coverage/types/` per the test contract above. Categories accepted by `validate_tag_format`: `stdlib`, `core`, `feature`. Tag format: `<category>:<snake_case_name>`.

## Resolution

Implemented `src/app/doc_coverage/analysis/sdoctest_coverage.spl` and shared
doc coverage types in pure Simple under `src/app/doc_coverage/types/`.

Verification:

```bash
SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check \
  src/app/doc_coverage/types/doc_item.spl \
  src/app/doc_coverage/types/coverage_result.spl \
  src/app/doc_coverage/analysis/sdoctest_coverage.spl \
  src/app/doc_coverage/reporting/markdown_generator.spl \
  test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl \
  test/01_unit/app/doc_coverage/markdown_report_spec.spl

SIMPLE_LIB=/tmp/simple-macro-intro-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple run \
  test/01_unit/app/doc_coverage/sdoctest_coverage_spec.spl
```
