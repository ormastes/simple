# Calc Formula Display Functions Test Plan

## Unit Coverage

- `COUNTA(A1:A4)` counts non-empty display values in a range, including a
  formula cell evaluated through the display path.
- `COUNTA(A1:A4,B1,"x","")` counts mixed range/cell/literal arguments and
  ignores empty string literals.
- `LEN`, `LOWER`, `UPPER`, and `TRIM` return deterministic text through
  `evaluate_formula_display_text`.
- `VLOOKUP` finds an exact first-column match, returns display text from the
  requested result column, resolves formula-valued return cells through the
  display path, and fails closed for missing keys, out-of-range columns, and
  unsupported approximate-match mode.
- `SheetsApp.confirm_edit()` writes display-safe `COUNTA`, exact-match
  `VLOOKUP`, and text-function results into formula `cached_display`, and the
  visible cell display reads those cached values after app-level recalc.
- Existing circular-reference display tests remain the regression gate for
  depth-bounded formula resolution.

## Evidence

- Unit spec:
  `test/01_unit/app/office/sheets/formula_harden_spec.spl`
- App-level unit spec:
  `test/01_unit/app/office/office_suite_spec.spl`
- Generated manual:
  `doc/06_spec/test/01_unit/app/office/sheets/formula_harden_spec.md`
- Generated app manual:
  `doc/06_spec/test/01_unit/app/office/office_suite_spec.md`

## Follow-Up

Full numeric function assertions, dependency-graph ordering, and cell-reference
numeric recalc assertions remain blocked by the tracked f64 backend issue.
