# Skip Keyword - Basic Functionality

Tests basic parsing and runtime behavior of the `skip` keyword as a standalone statement. Verifies that skip can be used in various contexts (if blocks, function bodies, loops), that it does not prevent subsequent code execution, does not affect return values, and does not alter variable scope.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-002 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/parser_skip_basic_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests basic parsing and runtime behavior of the `skip` keyword as a standalone
statement. Verifies that skip can be used in various contexts (if blocks,
function bodies, loops), that it does not prevent subsequent code execution,
does not affect return values, and does not alter variable scope.

## Syntax

```simple
skip
fn test_function():
skip
return "completed"
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/parser_skip_basic/result.json` |

## Scenarios

- parses skip as standalone statement
- parses skip with pass
- parses skip in if block
- parses skip in function body
- parses multiple skip statements
- parses skip before expression
- parses skip in loop
- skip does not prevent execution
- skip does not affect return value
- skip does not affect variable scope
