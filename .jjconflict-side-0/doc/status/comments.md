# Feature #22: Comments

**Status**: Implemented
**Difficulty**: 1
**Importance**: 5

## Summary

Line comments starting with `#` are supported.

## Syntax

```simple
# This is a comment
let x = 42  # inline comment

# Multi-line comments use multiple #
# Line 1
# Line 2
```

## Features

- [x] Line comments with `#`
- [x] Inline comments after code
- [x] Comments ignored in indentation handling

## Implementation

- **Lexer**: `skip_comment()` consumes until newline
- Comments are not tokenized (skipped entirely)
