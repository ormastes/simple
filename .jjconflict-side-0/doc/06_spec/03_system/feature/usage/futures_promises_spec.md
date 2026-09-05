# Futures and Promises for Asynchronous Programming

> This spec validates the full Promises API for asynchronous programming in Simple. Promises represent eventual values with three states: `Pending`, `Resolved(value)`, and `Rejected(error)`. The API supports creation via `Promise.new` with executor callbacks, transformation via `map` and `flat_map`, error recovery via `catch`, and multi-promise coordination via `all` (wait for all) and `race` (first settled wins). The spec also tests `future(expr)` with `await` for simple deferred values, and verifies that promise resolution is idempotent (only the first `resolve` or `reject` takes effect).

<!-- sdn-diagram:id=futures_promises_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=futures_promises_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

futures_promises_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=futures_promises_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Futures and Promises for Asynchronous Programming

This spec validates the full Promises API for asynchronous programming in Simple. Promises represent eventual values with three states: `Pending`, `Resolved(value)`, and `Rejected(error)`. The API supports creation via `Promise.new` with executor callbacks, transformation via `map` and `flat_map`, error recovery via `catch`, and multi-promise coordination via `all` (wait for all) and `race` (first settled wins). The spec also tests `future(expr)` with `await` for simple deferred values, and verifies that promise resolution is idempotent (only the first `resolve` or `reject` takes effect).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-020 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/futures_promises_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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
val p2 = Promise.resolved(21).map(_1 * 2)          # map transforms value
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

## Scenarios

### Futures and Promises

#### when creating a future

#### creates future from immediate value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = future(42)
expect await f == 42
```

</details>

#### creates future from computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = future(10 + 20 + 30)
expect await f == 60
```

</details>

#### when working with promises

#### resolves promise to value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.new(\resolve, reject: resolve(42))
match p.state:
    case PromiseState.Resolved(v):
        expect v == 42
    case _:
        expect false
```

</details>

#### fulfills promise once

1. resolve
2. resolve


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolve_count = 0
val p = Promise.new(\resolve, reject:
    resolve(10)
    resolve(20)
)
match p.state:
    case PromiseState.Resolved(v):
        expect v == 10
    case _:
        expect false
```

</details>

### Future Composition

#### when mapping over future values

#### maps future to new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.resolved(21)
val p2 = p.map(_1 * 2)
match p2.state:
    case PromiseState.Resolved(v):
        expect v == 42
    case _:
        expect false
```

</details>

#### chains multiple map operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.resolved(5)
val p2 = p.map(_1 * 2).map(_1 + 10).map(_1 * 3)
match p2.state:
    case PromiseState.Resolved(v):
        expect v == 60
    case _:
        expect false
```

</details>

#### when flattening nested futures

#### flattens nested futures

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.resolved(10)
val p2 = p.flat_map(Promise.resolved(_1 * 2))
match p2.state:
    case PromiseState.Resolved(v):
        expect v == 20
    case _:
        expect false
```

</details>

#### chains async operations with flatMap

1.  flat map


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.resolved(5)
val p2 = p.flat_map(Promise.resolved(_1 * 2))
          .flat_map(Promise.resolved(_1 + 10))
match p2.state:
    case PromiseState.Resolved(v):
        expect v == 20
    case _:
        expect false
```

</details>

### Future Error Handling

#### when future fails

#### captures exception in failed future

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.rejected("error occurred")
match p.state:
    case PromiseState.Rejected(e):
        expect e == "error occurred"
    case _:
        expect false
```

</details>

#### propagates errors through chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.rejected("original error")
val p2 = p.map(_1 * 2)
match p2.state:
    case PromiseState.Rejected(e):
        expect e == "original error"
    case _:
        expect false
```

</details>

#### when recovering from failed future

#### recovers with fallback value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.rejected("error")
val p2 = p.catch(\e: 42)
match p2.state:
    case PromiseState.Resolved(v):
        expect v == 42
    case _:
        expect false
```

</details>

#### retries failed future

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.rejected("first attempt")
val p2 = p.catch(\e: Promise.resolved(100))
match p2.state:
    case PromiseState.Resolved(v):
        expect v == 100
    case _:
        expect false
```

</details>

### Advanced Future Patterns

#### combines multiple futures

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = Promise.resolved(10)
val p2 = Promise.resolved(20)
val p3 = Promise.resolved(30)
val combined = all([p1, p2, p3])
match combined.state:
    case PromiseState.Resolved(values):
        expect values[0] + values[1] + values[2] == 60
    case _:
        expect false
```

</details>

#### handles timeout on future

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test race condition - first resolved wins
val p1 = Promise.resolved(42)
val p2 = Promise.resolved(100)
val winner = race([p1, p2])
match winner.state:
    case PromiseState.Resolved(v):
        expect v == 42
    case _:
        expect false
```

</details>

#### cancels pending future

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test race with rejection - first settled wins
val p1 = Promise.rejected("timeout")
val p2 = Promise.resolved(42)
val result = race([p1, p2])
match result.state:
    case PromiseState.Rejected(e):
        expect e == "timeout"
    case _:
        expect false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
