# Feature #8: Indentation-Based Blocks

**Status**: Implemented
**Difficulty**: 4
**Importance**: 4

## Summary

Simple uses Python-style indentation for block structure instead of braces.

## Syntax

```simple
fn example():
    if condition:
        do_something()
        do_more()
    else:
        alternative()

    for i in range(10):
        process(i)
```

## Features

- [x] INDENT token generation on increased indentation
- [x] DEDENT token generation on decreased indentation
- [x] Multiple DEDENT tokens for multi-level unindent
- [x] Tab expansion (tab = 4 spaces)
- [x] Empty lines ignored in indentation
- [x] Comment lines ignored in indentation
- [x] DEDENT generation at EOF

## Implementation

- **Lexer**: `handle_indentation()` tracks indent stack
- **Tokens**: `TokenKind::Indent`, `TokenKind::Dedent`, `TokenKind::Newline`
- **Stack**: `indent_stack: Vec<usize>` tracks current nesting
- **Parser**: Uses INDENT/DEDENT to delimit blocks

## Tests

- `lexer::tests::test_indent_dedent`
- `lexer::tests::test_nested_indent`
- Various function/control flow tests
