# TreeSitter Error Handling and Edge Cases Specification

Tests error handling and edge cases in the compiler.treesitter outline parser,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-ERR-001 to #TS-ERR-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_error_recovery_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests error handling and edge cases in the compiler.treesitter outline parser,
including ParseError collection, recovery after errors, doc comment
accumulation, and various declaration modifiers.

## API

```simple
use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/treesitter_error_recovery/result.json` |

## Scenarios

- produces empty module for empty source
- produces empty module for whitespace only
- produces empty module for comments only
- parses three functions
- preserves function names
- parses extern fn
- parses extern fn with params
- parses static method in impl
- parses mutable method in impl
- attaches doc comment to function
- attaches doc comment to struct
- continues parsing after valid declarations
- parses complex source without crashing
- parses trait followed by impl
- parses impl methods
