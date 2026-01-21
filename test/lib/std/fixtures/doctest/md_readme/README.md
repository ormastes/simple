<!--doctest:config
lang: simple
timeout: 5000
-->

# Test Documentation

This README.md demonstrates the doctest discovery system.

## Subdirectory

- [API](api/)

## Files

- [Usage](usage.md)

---

## Examples

### Basic Arithmetic

```simple
# doctest
let x = 1 + 1
# expected: 2
x
```

### More Arithmetic

```simple
# doctest
let y = 10 - 3
# expected: 7
y
```
