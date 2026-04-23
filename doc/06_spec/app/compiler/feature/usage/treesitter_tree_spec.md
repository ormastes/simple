# TreeSitter OutlineModule Structure Specification

Tests that TreeSitter parses source into correct OutlineModule structure,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-TREE-001 to #TS-TREE-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_tree_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that TreeSitter parses source into correct OutlineModule structure,
including function, class, struct, enum, import, and export outlines.

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
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/treesitter_tree/result.json` |

## Scenarios

- parses a simple function
- parses function with parameters
- parses extern function
- parses multiple functions
- parses a simple class
- parses class fields
- parses a simple struct
- parses struct fields
- parses a simple enum
- parses enum variants
- parses use statement
- parses export statement
- parses mixed declarations
- produces empty module for empty source
