# Feature #23: Line Continuation

**Status**: Implemented
**Difficulty**: 2
**Importance**: 2

## Summary

Backslash at end of line continues the expression to the next line.

## Syntax

```simple
let result = very_long_function_name() \
    + another_long_value \
    + final_value

some_function(arg1, arg2, \
    arg3, arg4)
```

## Features

- [x] Backslash-newline continuation
- [x] Works in expressions
- [x] Works in function calls

## Tests

- `interpreter_line_continuation_expression`
- `interpreter_line_continuation_function_call`

## Implementation

- **Lexer**: When `\` followed by `\n`, skip both and continue tokenizing
