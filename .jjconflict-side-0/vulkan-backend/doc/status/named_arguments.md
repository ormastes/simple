# Feature #18: Named Arguments

**Status**: Implemented
**Difficulty**: 2
**Importance**: 3

## Summary

Function calls support named arguments for clarity and flexibility.

## Syntax

```simple
fn greet(name, greeting = "Hello"):
    return f"{greeting}, {name}!"

# Positional
greet("World")

# Named
greet(name: "World", greeting: "Hi")

# Mixed (positional first, then named)
greet("World", greeting: "Hi")

# Reordered with named
greet(greeting: "Hi", name: "World")
```

## Features

- [x] Named argument syntax `name: value`
- [x] Mixed positional and named arguments
- [x] Argument reordering with named args
- [x] Default parameter values
- [x] Override default values

## Tests

- `interpreter_named_arguments_basic`
- `interpreter_named_arguments_mixed`
- `interpreter_named_arguments_reorder`
- `interpreter_default_arguments`
- `interpreter_default_arguments_override`

## Implementation

- **Parser**: `parse_arguments()` handles `name: value` syntax
- **AST**: `Argument { name: Option<String>, value: Expr }`
- **Interpreter**: `bind_args()` matches named args to parameters
