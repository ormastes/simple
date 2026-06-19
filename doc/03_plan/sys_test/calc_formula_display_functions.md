# Calc Formula Display Functions Test Plan

## Unit Coverage

- `COUNTA(A1:A4)` counts non-empty display values in a range, including a
  formula cell evaluated through the display path.
- `COUNTA(A1:A4,B1,"x","")` counts mixed range/cell/literal arguments and
  ignores empty string literals.
- `LEN`, `LOWER`, `UPPER`, and `TRIM` return deterministic text through
  `evaluate_formula_display_text`.
- Existing circular-reference display tests remain the regression gate for
  depth-bounded formula resolution.

## Evidence

- Unit spec:
  `test/01_unit/app/office/sheets/formula_harden_spec.spl`
- Generated manual:
  `doc/06_spec/test/01_unit/app/office/sheets/formula_harden_spec.md`

## Follow-Up

Full numeric function assertions and recalc correctness remain blocked by the
tracked f64 backend issue.
