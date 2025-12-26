# Feature #20: Functional Update Operator

**Status**: Implemented
**Difficulty**: 2
**Importance**: 3

## Summary

The `->` operator provides syntactic sugar for reassigning the result of a method call back to the target.

## Syntax

```simple
# target->method(args) desugars to: target = target.method(args)

let mut list = [1, 2, 3]
list->append(4)        # list = list.append(4)
list->sort()           # list = list.sort()
list->reverse()        # list = list.reverse()

# Chaining
list->filter(\x: x > 0)->map(\x: x * 2)->sort()
```

## Features

- [x] Basic functional update `target->method(args)`
- [x] Chained updates
- [x] Works with arrays, dicts, strings
- [x] Mutability checking (requires `let mut`)
- [x] Prevents update on const variables

## Tests

- `interpreter_functional_update_array_concat`
- `interpreter_functional_update_array_map`
- `interpreter_functional_update_array_filter`
- `interpreter_functional_update_dict_set`
- `interpreter_functional_update_chained`

## Implementation

- **Lexer**: `TokenKind::Arrow` for `->`
- **Parser**: `Expr::FunctionalUpdate { target, method, args }`
- **Interpreter**: Desugars to method call + assignment in `exec_node()`
