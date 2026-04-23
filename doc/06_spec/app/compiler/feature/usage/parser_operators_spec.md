# Parser Operator Specification

Tests that the parser correctly tokenizes and parses all operators

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-OP-001 to #PARSER-OP-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_operators_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that the parser correctly tokenizes and parses all operators
including arithmetic, comparison, logical, bitwise, and special operators.

## Syntax

```simple
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/parser_operators/result.json` |

## Scenarios

- parses addition
- parses subtraction
- parses multiplication
- parses division
- parses modulo
- parses power
- parses integer division
- parses less than
- parses greater than
- parses less than or equal
- parses greater than or equal
- parses equality
- parses inequality
- parses and
- parses or
- parses not
- parses combined logical
- parses bitwise and
- parses bitwise or
- parses bitwise xor
- parses bitwise not
- parses left shift
- parses right shift
- parses simple assignment
- parses add-assign
- parses sub-assign
- parses mul-assign
- parses div-assign
- parses mod-assign
- parses suspend-assign
- parses pipe forward
- parses optional chaining
- parses null coalescing
- parses existence check
- parses negated existence
- parses try operator
- parses exclusive range
- parses inclusive range
- parses range in slice
- power before multiplication
- multiplication before addition
- comparison after arithmetic
- logical after comparison
- parentheses override precedence
- complex expression precedence
- parses matrix multiplication
- parses broadcast operators
- parses layer connect
