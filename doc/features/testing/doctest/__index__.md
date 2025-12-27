# Doctest Framework (#192-#197)

Documentation testing framework for code examples in doc comments.

## Features

| ID | Feature | Difficulty | Status | Impl |
|----|---------|------------|--------|------|
| #192 | `>>>` prompt | 3 | ✅ | R |
| #193 | Expected output | 2 | ✅ | R |
| #194 | `...` continuation | 2 | ✅ | R |
| #195 | `# doctest: +SKIP` | 2 | ✅ | R |
| #196 | `# doctest: +ELLIPSIS` | 2 | ✅ | R |
| #197 | FFI integration | 3 | ✅ | R |

## Summary

**Status:** 6/6 Complete (100%)

## Example

```simple
/// Adds two numbers.
///
/// >>> add(1, 2)
/// 3
///
/// >>> add(-1, 1)
/// 0
fn add(a: i64, b: i64) -> i64:
    return a + b
```

## Documentation

- [system_test.md](../../../guides/system_test.md) - System test framework

## Test Locations

- **Simple Tests:** `simple/std_lib/test/system/doctest/`
- **Rust Tests:** `src/driver/tests/`
