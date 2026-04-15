# TreeSitter Heuristic Mode Specification

Tests heuristic (line-based) parsing mode of the TreeSitter parser.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-CURSOR-001 to #TS-CURSOR-015 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_cursor_spec.spl` |
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

Tests heuristic (line-based) parsing mode of the TreeSitter parser.
Heuristic mode uses simple line scanning instead of full tokenization,
providing error-tolerant results even with malformed input.

## API

```simple
use compiler.treesitter.*
use compiler.core.lexer.*

var ts = TreeSitter(
lexer: lexer_new(source),
current: lex_token_eof(1),
previous: lex_token_eof(1),
errors: [],
doc_comment: nil,
inline_blocks: [],
current_context: nil,
fast_mode: false,
heuristic_mode: true,
registry: nil
)
val outline = ts.parse_outline()
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/treesitter_cursor/result.json` |

## Scenarios

- parses fn declaration
- parses multiple functions
- parses class declaration
- parses struct declaration
- parses enum declaration
- parses trait declaration
- parses impl block
- parses impl with multiple members
- detects pub function
- detects pub struct
- handles empty source
- skips unrecognized lines
- parses mixed valid and invalid
