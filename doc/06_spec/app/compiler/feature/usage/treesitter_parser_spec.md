# TreeSitter Parser Specification

Tests the basic TreeSitter.new(source).parse_outline() workflow,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-PARSER-001 to #TS-PARSER-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_parser_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests the basic TreeSitter.new(source).parse_outline() workflow,
verifying that source code is correctly parsed into an OutlineModule.

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
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/treesitter_parser/result.json` |

## Scenarios

- creates parser from source
- creates parser from empty source
- parses single function
- parses function with return type
- parses function with parameters
- parses struct with fields
- parses enum with variants
- parses use statement
- parses export statement
- parses function and struct
- parses function, struct, and enum
- parses function with impl
- returns empty outline for empty source
