# Futures and Promises for Asynchronous Programming

This spec validates the full Promises API for asynchronous programming in Simple. Promises represent eventual values with three states: `Pending`, `Resolved(value)`, and `Rejected(error)`. The API supports creation via `Promise.new` with executor callbacks, transformation via `map` and `flat_map`, error recovery via `catch`, and multi-promise coordination via `all` (wait for all) and `race` (first settled wins). The spec also tests `future(expr)` with `await` for simple deferred values, and verifies that promise resolution is idempotent (only the first `resolve` or `reject` takes effect).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/feature/usage/futures_promises_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

This spec validates the full Promises API for asynchronous programming in Simple.
Promises represent eventual values with three states: `Pending`, `Resolved(value)`,
and `Rejected(error)`. The API supports creation via `Promise.new` with executor
callbacks, transformation via `map` and `flat_map`, error recovery via `catch`,
and multi-promise coordination via `all` (wait for all) and `race` (first settled wins).
The spec also tests `future(expr)` with `await` for simple deferred values, and verifies
that promise resolution is idempotent (only the first `resolve` or `reject` takes effect).

## Syntax

```simple
val p = Promise.new(\resolve, reject: resolve(42))
val p2 = Promise.resolved(21).map(\x: x * 2)       # map transforms value
val p3 = Promise.rejected("error").catch(\e: 42)    # catch recovers

val combined = all([p1, p2, p3])        # wait for all promises
val winner = race([fast, slow])         # first settled wins

val f = future(10 + 20 + 30)
expect await f == 60                     # future with await
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `Promise.new` | Creates a promise with an executor callback receiving `resolve` and `reject` |
| `Promise.resolved` | Creates an immediately resolved promise with a value |
| `Promise.rejected` | Creates an immediately rejected promise with an error |
| `map` / `then` | Transforms a resolved value, propagating rejections unchanged |
| `flat_map` | Chains promises that return promises, flattening the result |
| `catch` | Recovers from a rejected promise by providing a fallback value |
| `all` | Combines multiple promises; resolves when all resolve, rejects on first failure |
| `race` | Returns the first settled promise (resolved or rejected) from a list |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/futures_promises/result.json` |

## Scenarios

- creates future from immediate value
- creates future from computation
- resolves promise to value
- fulfills promise once
- maps future to new value
- chains multiple map operations
- flattens nested futures
- chains async operations with flatMap
- captures exception in failed future
- propagates errors through chain
- recovers with fallback value
- retries failed future
- combines multiple futures
- handles timeout on future
- cancels pending future
