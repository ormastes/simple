# TreeSitter Lexer Specification

Tests the core.lexer tokenization used by compiler.treesitter,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-LEX-001 to #TS-LEX-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_lexer_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests the core.lexer tokenization used by compiler.treesitter,
including keyword, identifier, number, operator, and delimiter tokens.

## API

```simple
use compiler.core.lexer.{Lexer, lexer_new, lexer_next_token, Token, TokenKind}

var lexer = lexer_new(source)
val token = lexer_next_token(lexer)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/treesitter_lexer/result.json` |

## Scenarios

- tokenizes fn keyword
- tokenizes val keyword
- tokenizes var keyword
- tokenizes if keyword
- tokenizes struct keyword
- tokenizes enum keyword
- tokenizes impl keyword
- tokenizes trait keyword
- tokenizes simple identifier
- tokenizes identifier with underscore
- tokenizes identifier with digits
- tokenizes integer
- tokenizes float
- tokenizes zero
- tokenizes plus
- tokenizes minus
- tokenizes star
- tokenizes colon
- tokenizes arrow
- tokenizes left paren
- tokenizes right paren
- tokenizes left brace
- tokenizes right brace
- tokenizes left bracket
- tokenizes right bracket
- tokenizes function signature
- tokenizes variable declaration
- produces EOF for empty input
- produces EOF after all tokens consumed
