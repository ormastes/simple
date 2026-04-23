# Effect Annotations Specification

Tests that effect annotations (@pure, @io, @net, @fs, @unsafe, @async)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EFFECT-ANN-001 to #EFFECT-ANN-012 |
| Category | Type System \| Effects |
| Status | Implemented |
| Source | `test/feature/usage/effect_annotations_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that effect annotations (@pure, @io, @net, @fs, @unsafe, @async)
are correctly parsed and applied to functions.

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
fn fetch_and_log(url: text):
val data = http_get(url)
print(data)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/effect_annotations/result.json` |

## Scenarios

- parses @pure on function
- pure function has no side effects
- parses @io on function
- parses @net on function
- parses @fs on function
- parses @unsafe on function
- parses @async on function
- parses two effects
- parses three effects
- parses io and fs together
- function with no effects parses
- no-effect function can call anything
- combines @pure with @inline
- combines @io with @deprecated
- effects separate from other decorators
- Effect has Pure variant
- Effect has Io variant
- Effect has Net variant
- Effect has Fs variant
- Effect has Unsafe variant
- Effect has Async variant
- converts 'pure' to Pure
- converts 'io' to Io
- converts 'net' to Net
- converts 'fs' to Fs
- converts 'unsafe' to Unsafe
- converts 'async' to Async
- returns None for unknown
- returns None for inline
- Pure decorator name is 'pure'
- Io decorator name is 'io'
- Net decorator name is 'net'
- Fs decorator name is 'fs'
- Unsafe decorator name is 'unsafe'
- Async decorator name is 'async'
