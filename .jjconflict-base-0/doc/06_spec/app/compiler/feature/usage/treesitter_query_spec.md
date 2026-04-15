# TreeSitter Advanced Outline Parsing Specification

Tests advanced outline features: type parameters, traits, impls,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-QUERY-001 to #TS-QUERY-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_query_spec.spl` |
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

Tests advanced outline features: type parameters, traits, impls,
type aliases, and constants.

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
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/treesitter_query/result.json` |

## Scenarios

- parses struct with type parameter
- parses class with multiple type parameters
- parses trait with methods
- parses empty trait
- parses impl with methods
- parses impl with static method
- parses type alias
- parses val declaration
- parses var declaration
- parses traits and impls together
