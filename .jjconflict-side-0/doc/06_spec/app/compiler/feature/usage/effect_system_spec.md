# Effect System Specification

Tests the effect system including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EFFECT-SYS-001 to #EFFECT-SYS-040 |
| Category | Type System \| Effects |
| Status | Implemented |
| Source | `test/feature/usage/effect_system_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests the effect system including:
- @pure, @io, @net, @fs, @unsafe, @async effects
- Effect propagation and call restrictions
- Capability requirements and validation
- Stacked effects

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
fn fetch_and_log(url: text) -> text:
val data = http_get(url)
print(data)
data
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/effect_system/result.json` |

## Scenarios

- pure function can do computation
- pure function can call other pure functions
- pure function blocks print
- io function can do computation
- async decorator syntax works
- async allows non-blocking io
- fs function can do computation
- net function can do computation
- unsafe function can do computation
- pure and async together
- io and net together
- all effects together
- all effects parsed
- effects with inline attribute
- unrestricted function works
- pure cannot call io
- pure cannot call net
- pure cannot call fs
- pure cannot call unsafe
- io can call pure
- io can call io
- unrestricted can call anything
- basic capability parsing
- multiple capabilities
- all capabilities
- trailing comma allowed
- empty requires list
- effect matches capability
- io effect blocked by pure-only module
- async always allowed
- multiple effects with matching capabilities
- unrestricted module allows all
