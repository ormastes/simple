# Calc Formula Display Functions Design

## Scope

This slice hardens Calc by adding runner-verifiable formula functions to
`evaluate_formula_display_text`. The normal `evaluate_formula` path still owns
the full recursive-descent parser and f64-returning `CellValue` results, but it
is not the verification surface while the tracked f64 backend issue is open.

## Display Function Dispatch

`evaluate_formula_display_text` tokenizes the formula and detects top-level
function calls of the form `NAME(...)`. It dispatches only display-safe
functions:

- `COUNTA` counts non-empty display values from ranges, cells, literals, and
  simple display expressions.
- `LEN` returns string length.
- `LOWER` and `UPPER` transform string case.
- `TRIM` removes leading and trailing whitespace.
- `VLOOKUP` performs exact first-column lookup over a rectangular range and
  returns display text from the requested 1-based result column.

Unsupported or malformed calls return an empty display string.

## Data Flow

Cell references are resolved through display text, not f64. Formula cells recurse
through `evaluate_formula_display_text` with the existing depth cap, preserving
the circular-reference guard. `COUNTA` ranges use `parse_range` and
`expand_range_refs` and count only non-empty display values. `VLOOKUP` uses the
same range parser, scans rows from the leftmost column, and rejects missing
matches, result columns outside the range, and approximate-match mode.

## Limits

Function composition is intentionally top-level only for this slice. Nested text
functions, approximate `VLOOKUP`, and full Excel-compatible function semantics
are follow-up work.
