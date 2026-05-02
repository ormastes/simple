# Effect System Specification

**Feature ID:** #EFFECT-SYS-001 to #EFFECT-SYS-040 | **Category:** Type System | Effects | **Status:** Implemented

_Source: `test/feature/usage/effect_system_spec.spl`_

---

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Capabilities

- `requires [cap1, cap2]` - Module capability requirements
- Effect validation at compile time

## Syntax

```simple
requires [pure, io]

@pure
fn add(x: i64, y: i64) -> i64:
    x + y

@io @net
fn fetch_and_log(url: str) -> str:
    val data = http_get(url)
    print(data)
    data
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 32 |

## Test Structure

### @pure Effect

- ✅ pure function can do computation
- ✅ pure function can call other pure functions
- ✅ pure function blocks print
### @io Effect

- ✅ io function can do computation
### @async Effect

- ✅ async decorator syntax works
- ✅ async allows non-blocking io
### @fs Effect

- ✅ fs function can do computation
### @net Effect

- ✅ net function can do computation
### @unsafe Effect

- ✅ unsafe function can do computation
### Stacked Effects

- ✅ pure and async together
- ✅ io and net together
- ✅ all effects together
- ✅ all effects parsed
### Effect with Attributes

- ✅ effects with inline attribute
### Unrestricted Functions

- ✅ unrestricted function works
### Effect Propagation

- ✅ pure cannot call io
- ✅ pure cannot call net
- ✅ pure cannot call fs
- ✅ pure cannot call unsafe
- ✅ io can call pure
- ✅ io can call io
- ✅ unrestricted can call anything
### Capability Requirements

- ✅ basic capability parsing
- ✅ multiple capabilities
- ✅ all capabilities
- ✅ trailing comma allowed
- ✅ empty requires list
### Compile-Time Capability Validation

- ✅ effect matches capability
- ✅ io effect blocked by pure-only module
- ✅ async always allowed
- ✅ multiple effects with matching capabilities
- ✅ unrestricted module allows all

