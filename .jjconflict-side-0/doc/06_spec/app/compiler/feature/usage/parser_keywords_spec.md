# Parser Keywords Specification

Tests that all Simple language keywords are correctly recognized and

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-KW-001 to #PARSER-KW-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_keywords_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that all Simple language keywords are correctly recognized and
parsed in their appropriate contexts.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_keywords/result.json` |

## Scenarios

- val declares immutable variable
- var declares mutable variable
- parses if statement
- parses elif statement
- parses while loop
- parses for loop
- parses break in loop
- parses continue in loop
- parses return statement
- parses match expression
- parses and operator
- parses or operator
- parses not operator
- parses in operator
- parses true
- parses false
- parses nil
- parses self in method
- parses fn declaration
- parses nested function
- parses lambda expression
- parses higher-order function
