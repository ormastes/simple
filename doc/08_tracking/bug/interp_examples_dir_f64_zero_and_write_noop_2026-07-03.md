# Bug: scripts under examples/ zero nested f64 payloads and no-op file writes

**Date:** 2026-07-03
**Severity:** high (silently wrong results)
**Status:** open

## Symptom
The identical Simple script produces different results depending on its
location on disk:

- run from `test/` (spec runner) or from a directory OUTSIDE the repo
  (e.g. /tmp): correct — `Sheet.set_value("B2", "1200")` stores 1200,
  `cell_display_text` shows `1200`, `std.io_runtime.write_file` writes.
- run from `examples/10_tooling/office_macros/`: every
  `CellValue.NumberVal(value: f64)` payload reads back as
  `0.00000000000000000` (raw float formatting, wrong code path), and
  `write_file` returns without creating the file.

## Repro
```
bin/simple run examples/10_tooling/office_macros/quarterly_report_macro.spl /tmp/out
# -> profit=0, no files written
cp examples/10_tooling/office_macros/quarterly_report_macro.spl /tmp/m.spl
bin/simple run /tmp/m.spl /tmp/out
# -> profit=400, budget.csv/report.md/budget.html/report.html all written
```

## Analysis
Related to interp_f64_nested_struct_payload_zero_2026-06-14 (f64 payloads in
nested struct/enum zero out) and the cross-module struct-name collision bug:
under the examples/ module-resolution context the office modules appear to
load through a second registration path, zeroing f64 enum payloads
(CellValue.NumberVal) and mis-dispatching number formatting. Outside the repo,
module resolution falls back to runtime loading and behaves correctly, as
does the test/ spec context.

## Impact
In-repo example scripts that exercise f64-carrying models give silently wrong
output. User macros outside the repo are unaffected.
