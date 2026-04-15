# Multi-line Syntax Specification

Tests for multi-line syntax patterns including function calls spanning multiple lines, array literals, and continuation lines.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MULTI-001 |
| Category | Language \| Syntax |
| Status | Implemented |
| Source | `test/feature/usage/multiline_syntax_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for multi-line syntax patterns including function calls spanning
multiple lines, array literals, and continuation lines.

## Syntax

```simple
val result = function_name(
arg1,
arg2,
arg3
)

val items = [
1,
2,
3
]

val sum = 1 + 2 + \
3 + 4
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/multiline_syntax/result.json` |

## Scenarios

- calls function with arguments on multiple lines
- calls function with named arguments on multiple lines
- nests function calls on single line
- nests function calls on multiple lines
- creates multi-line array literal
- creates multi-line struct initialization
- continues function call to next line
- continues call at same indent level
- destructures tuple from array element
- accesses tuple elements with dot notation
- destructures nested tuple data
