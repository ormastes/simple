# TreeSitter Lexer Specification

**Feature ID:** #TS-LEX-001 to #TS-LEX-020 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/treesitter_lexer_spec.spl`_

---

## API

```simple
use compiler_core.lexer.{Lexer, lexer_new, lexer_next_token, Token, TokenKind}

var lexer = lexer_new(source)
val token = lexer_next_token(lexer)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 29 |

## Test Structure

### Core Lexer Keyword Tokenization

- ✅ tokenizes fn keyword
- ✅ tokenizes val keyword
- ✅ tokenizes var keyword
- ✅ tokenizes if keyword
- ✅ tokenizes struct keyword
- ✅ tokenizes enum keyword
- ✅ tokenizes impl keyword
- ✅ tokenizes trait keyword
### Core Lexer Identifier Tokenization

- ✅ tokenizes simple identifier
- ✅ tokenizes identifier with underscore
- ✅ tokenizes identifier with digits
### Core Lexer Number Tokenization

- ✅ tokenizes integer
- ✅ tokenizes float
- ✅ tokenizes zero
### Core Lexer Operator Tokenization

- ✅ tokenizes plus
- ✅ tokenizes minus
- ✅ tokenizes star
- ✅ tokenizes colon
- ✅ tokenizes arrow
### Core Lexer Delimiter Tokenization

- ✅ tokenizes left paren
- ✅ tokenizes right paren
- ✅ tokenizes left brace
- ✅ tokenizes right brace
- ✅ tokenizes left bracket
- ✅ tokenizes right bracket
### Core Lexer Multi-Token Sequence

- ✅ tokenizes function signature
- ✅ tokenizes variable declaration
### Core Lexer EOF Token

- ✅ produces EOF for empty input
- ✅ produces EOF after all tokens consumed

