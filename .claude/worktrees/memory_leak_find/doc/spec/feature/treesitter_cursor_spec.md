# TreeSitter Heuristic Mode Specification

**Feature ID:** #TS-CURSOR-001 to #TS-CURSOR-015 | **Category:** Infrastructure | Parser | **Status:** Implemented

_Source: `test/feature/usage/treesitter_cursor_spec.spl`_

---

## API

```simple
use compiler.treesitter.*
use compiler_core.lexer.*

# Create heuristic-mode parser
var ts = TreeSitter(
    lexer: lexer_new(source),
    current: token_eof(0, 1),
    previous: token_eof(0, 1),
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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 13 |

## Test Structure

### Heuristic Function Parsing

- ✅ parses fn declaration
- ✅ parses multiple functions
### Heuristic Class Parsing

- ✅ parses class declaration
### Heuristic Struct Parsing

- ✅ parses struct declaration
### Heuristic Enum Parsing

- ✅ parses enum declaration
### Heuristic Trait Parsing

- ✅ parses trait declaration
### Heuristic Impl Parsing

- ✅ parses impl block
- ✅ parses impl with multiple members
### Heuristic Visibility Detection

- ✅ detects pub function
- ✅ detects pub struct
### Heuristic Error Tolerance

- ✅ handles empty source
- ✅ skips unrecognized lines
- ✅ parses mixed valid and invalid

