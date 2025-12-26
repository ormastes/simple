# Feature #47: No-Parentheses Calls

**Status**: Implemented
**Difficulty**: 3
**Importance**: 2

## Summary

Function calls at statement level can omit parentheses for a cleaner syntax.

## Syntax

```simple
# With parentheses
print("Hello")
len("test")

# Without parentheses (statement level)
print "Hello"
len "test"

# With multiple arguments
some_func arg1, arg2, arg3
```

## Features

- [x] Statement-level calls without parentheses
- [x] Works with string arguments
- [x] Works with integer arguments
- [x] Works with multiple arguments
- [x] Comma-separated arguments

## Tests

- `interpreter_no_paren_call_simple_statement`
- `interpreter_no_paren_call_with_string_arg`
- `interpreter_no_paren_call_with_int_arg`

## Implementation

- **Parser**: `can_start_argument()` checks if next token could be an argument
- **Parser**: `parse_no_paren_arguments()` parses arguments without parentheses
- Triggers when identifier followed by value-like token at statement level

## Limitations

- Only works at statement level (not in expressions)
- Requires careful grammar design to avoid ambiguity
