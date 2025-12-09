# Feature #36: Method Missing

**Status**: Implemented
**Difficulty**: 4
**Importance**: 2

## Summary

Classes can define a `method_missing` handler for dynamic method dispatch.

## Syntax

```simple
class Proxy:
    target: i64 = 0

    fn method_missing(self, name, args, block):
        # name: string - method name that was called
        # args: array - arguments passed
        # block: optional lambda block
        return 42

let p = Proxy { target: 0 }
p.anything()           # Calls method_missing("anything", [], nil)
p.compute(1, 2, 3)     # Calls method_missing("compute", [1, 2, 3], nil)
```

## Features

- [x] `method_missing(self, name, args, block)` signature
- [x] Called when method not found on class
- [x] Access to method name as string
- [x] Access to arguments as array
- [x] Works with context blocks

## Tests

- `interpreter_method_missing_basic`
- `interpreter_method_missing_with_args`
- `interpreter_method_missing_with_context`

## Implementation

- **Interpreter**: Check for `method_missing` in class methods when method not found
- Constructs args array and passes method name as first argument
