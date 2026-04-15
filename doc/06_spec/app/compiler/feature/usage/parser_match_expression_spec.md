# Match Expression Separator Specification

The runtime has two match parsers:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-ME-001 to #PARSER-ME-010 |
| Category | Infrastructure \| Parser |
| Status | In Progress |
| Source | `test/feature/usage/parser_match_expression_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Bug: Match arm separators in expression context

The runtime has two match parsers:
1. Statement-level: `case` keyword + `:` (works, but no return value)
2. Expression-level: only `=>` works (returns value, rejects `:` and `case`)

The expression-level parser should also accept `:` and `case` keyword.
Fix: src/app/parser/expr/control.spl lines 78-94

Broken syntax (expression context):
val y = match x:
42: "found"           # error: expected FatArrow, found Colon
val y = match x:
case 42: "found"     # error: expected pattern, found Case

After rebuild, uncomment skipped tests in Group 3 below.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_match_expression/result.json` |

## Scenarios

- executes matching arm for integer patterns
- executes arm with guard clauses
- single-expression arms return values
- multi-line arm bodies return last expression
- multiple statements in arm body
- guard clauses select correct arm
- nested match expressions return values
- expression and statement match get same answers
- expression match multi-line returns correct value
