# Calc Formula Display Functions Requirements

## Functional Requirements

- CALC-FUNC-001: The formula display path supports `COUNTA` over cell ranges
  and literal arguments, counting non-empty values only.
- CALC-FUNC-002: The formula display path supports text functions `LEN`,
  `LOWER`, `UPPER`, and `TRIM` over string literals and cell display text.
- CALC-FUNC-003: Display-safe functions return deterministic text so Calc UI
  and tests can verify behavior while the f64 formula-return path remains
  blocked by the current backend issue.
- CALC-FUNC-004: The formula display path supports exact-match `VLOOKUP`
  over a rectangular table range, returning display text from a 1-based result
  column in the matched row.

## Out of Scope

Full Excel-compatible function coverage, approximate `VLOOKUP`, nested text
function calls, and f64-returning numeric verification remain follow-up work.
