# Line Continuation Specification

Line continuation allows long expressions and function calls to span multiple lines

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2400 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/line_continuation_spec.spl` |
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

Line continuation allows long expressions and function calls to span multiple lines
using explicit backslash (`\`) at end of line. This enables clean formatting of
complex expressions without exceeding line length limits.

## Syntax

```simple
val sum = value1 + \
value2 + \
value3

val result = add(1, \
2, \
3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Explicit Continuation | Backslash at line end forces continuation to next line |
| Nesting | Multiple levels of continuation allowed |
| Indentation | Improves readability but not required for continuation |

## Behavior

Line continuation:
- Backslash at end of line continues expression to next line
- Multiple continuations can be chained
- Works in expressions and function calls
- Preserves semantic meaning across line boundaries

## Note

Implicit continuation (just newlines inside parentheses/brackets/braces) is not
currently supported. Use explicit backslash continuation instead.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/line_continuation/result.json` |

## Scenarios

- continues expression with backslash
- continues function call with backslash
- combines backslash and arithmetic
- chains multiple continuations
- continues binary operation
- continues comparison
- continues string concatenation
- works with any indentation level
- continues deeply indented code
- formats long arithmetic expression
- formats function with many arguments
