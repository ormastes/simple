# CMM Expression Parser Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CMM-EXPR |
| Category | Tooling |
| Status | Implemented |
| Source | `test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 80 |
| Active scenarios | 80 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cmm_lsp/cmm_parser_expr/result.json` |

## Scenarios

- parses addition
- parses subtraction
- parses multiplication
- parses division
- parses modulo
- parses chained addition
- parses mixed arithmetic
- parses equality
- parses not-equal
- parses less-than
- parses greater-than
- parses less-than-or-equal
- parses greater-than-or-equal
- parses logical AND
- parses logical OR
- parses logical XOR
- parses bitwise AND
- parses bitwise OR
- parses bitwise XOR
- parses shift left
- parses shift right
- parses unary minus
- parses bitwise NOT
- parses logical NOT
- parses double unary minus
- parses range-to expression
- parses range-offset expression
- parses range-dots expression
- parses range with hex endpoints
- parses range with decimal endpoints
- parses Register function
- parses CPU function
- parses TRUE function
- parses FALSE function
- parses dot-path function call
- parses function with multiple arguments
- parses function with macro argument
- parses nested function calls
- parses parenthesized expression
- parses nested parentheses
- parses braced expression for constant conversion
- parses hex literal in assignment
- parses binary literal in assignment
- parses decimal literal in assignment
- parses float literal in assignment
- parses plain integer in assignment
- parses string literal in assignment
- parses char literal in assignment
- parses time literal in assignment
- parses hex mask literal in assignment
- parses binary mask literal in assignment
- parses simple macro ref as expression
- parses recursive macro ref as expression
- parses macro in arithmetic
- parses macro in comparison
- parses data access class address
- parses program access class address
- parses option flag as expression
- parses multiple option flags
- parses file channel in expression
- parses file channel number 2
- parses dot path as expression
- parses SYStem.state as expression
- multiplication has higher precedence than addition
- comparison has lower precedence than addition
- logical AND has lower precedence than comparison
- logical OR has lower precedence than logical AND
- shift has higher precedence than addition
- parentheses override precedence
- parses complex arithmetic with macros
- parses function call result in arithmetic
- parses braced subexpression in range
- parses comparison with hex in IF
- parses string concat with plus
- parses classic AND in expression
- parses classic OR in expression
- parses classic XOR in expression
- parses bare identifier as command parameter
- parses multiple bare identifiers as parameters
- parses identifier in register call
