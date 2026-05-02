# Effect Annotations Specification

**Feature ID:** #EFFECT-ANN-001 to #EFFECT-ANN-012 | **Category:** Type System | Effects | **Status:** Implemented

_Source: `test/feature/usage/effect_annotations_spec.spl`_

---

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Syntax

```simple
@pure
fn add(x: i64, y: i64) -> i64:
    x + y

@io @net
fn fetch_and_log(url: str):
    val data = http_get(url)
    print(data)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 35 |

## Test Structure

### Single Effect Annotations

#### @pure effect

- ✅ parses @pure on function
- ✅ pure function has no side effects
#### @io effect

- ✅ parses @io on function
#### @net effect

- ✅ parses @net on function
#### @fs effect

- ✅ parses @fs on function
#### @unsafe effect

- ✅ parses @unsafe on function
#### @async effect

- ✅ parses @async on function
### Multiple Effect Annotations

- ✅ parses two effects
- ✅ parses three effects
- ✅ parses io and fs together
### Functions Without Effects

- ✅ function with no effects parses
- ✅ no-effect function can call anything
### Effects with Other Decorators

- ✅ combines @pure with @inline
- ✅ combines @io with @deprecated
- ✅ effects separate from other decorators
### Effect Enum

- ✅ Effect has Pure variant
- ✅ Effect has Io variant
- ✅ Effect has Net variant
- ✅ Effect has Fs variant
- ✅ Effect has Unsafe variant
- ✅ Effect has Async variant
### Effect from Decorator Name

- ✅ converts 'pure' to Pure
- ✅ converts 'io' to Io
- ✅ converts 'net' to Net
- ✅ converts 'fs' to Fs
- ✅ converts 'unsafe' to Unsafe
- ✅ converts 'async' to Async
- ✅ returns None for unknown
- ✅ returns None for inline
### Effect Decorator Name

- ✅ Pure decorator name is 'pure'
- ✅ Io decorator name is 'io'
- ✅ Net decorator name is 'net'
- ✅ Fs decorator name is 'fs'
- ✅ Unsafe decorator name is 'unsafe'
- ✅ Async decorator name is 'async'

