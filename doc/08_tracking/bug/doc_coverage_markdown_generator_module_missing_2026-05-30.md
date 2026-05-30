# doc_coverage markdown_generator and types modules missing

Date: 2026-05-30
Status: Open
Severity: High

## Symptom

`test/unit/app/doc_coverage/markdown_report_spec.spl` fails with:

```
Cannot resolve module: doc_coverage.reporting.markdown_generator
```

The test also imports `doc_coverage.types.coverage_result.{CoverageReport, FileCoverage}` and `doc_coverage.types.doc_item.{DocItem}` (all without `app.` or `std.` prefix — the module resolver reports these as unresolvable starting from the test file's directory).

## Evidence

- `find src/ -name '*markdown_generator*'` — no results.
- `find src/ -name '*coverage_result*' | grep -v node_modules` — no results.
- `grep -rn 'fn generate_coverage_markdown' src/ --include='*.spl'` — no results.
- `grep -rn 'struct CoverageReport' src/ --include='*.spl'` — only in unrelated compiler coverage tools, not under `doc_coverage`.
- The error message shows the resolver looks at `test/unit/app/doc_coverage/doc_coverage` — confirming no `app.` or `std.` prefix was used.

## Required modules and symbols

The test expects (with corrected `app.` prefix):
- `app.doc_coverage.reporting.markdown_generator` exporting:
  - `fn generate_coverage_markdown(report: CoverageReport) -> text`
- `app.doc_coverage.types.coverage_result` exporting:
  - `struct CoverageReport` with fields: `total_items`, `documented_items`, `missing_docs`, `sdoctest_coverage`, `missing_sdoctest`, `timestamp`, and a file list
  - `struct FileCoverage` with fields: `total_items`, `documented_items`, `missing_docs`, `has_sdoctest`, `missing_sdoctest`
- `app.doc_coverage.types.doc_item` exporting:
  - `struct DocItem`

## Additional issue

The test file uses bare `doc_coverage.reporting.markdown_generator` (no `app.` or `std.` prefix). This is also a bug in the import statement — it should be `app.doc_coverage.reporting.markdown_generator` once the modules exist.

## Expected

`src/app/doc_coverage/reporting/markdown_generator.spl` and `src/app/doc_coverage/types/coverage_result.spl` implementing the above symbols, plus the test's import corrected to use `app.` prefix.

## Next Probe

1. Implement the missing modules.
2. Fix import paths in `test/unit/app/doc_coverage/markdown_report_spec.spl` to use `app.` prefix.
