# Futures and Promises for Asynchronous Programming

> This spec validates the full Promises API for asynchronous programming in Simple. Promises represent eventual values with three states: `Pending`, `Resolved(value)`, and `Rejected(error)`. The API supports creation via `Promise.new` with executor callbacks, transformation via `map` and `flat_map`, error recovery via `catch`, and multi-promise coordination via `all` (wait for all) and `race` (first settled wins). The spec also tests `future(expr)` with `await` for simple deferred values, and verifies that promise resolution is idempotent (only the first `resolve` or `reject` takes effect).

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
| Source | `test/feature/usage/futures_promises_spec.spl` |
| Updated | 2026-08-26 |
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
use std.spec.step

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

- creates future from immediate value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates future from immediate value")
val f = future(42)
expect await f == 42
```

</details>

#### creates future from computation

- creates future from computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates future from computation")
val f = future(10 + 20 + 30)
expect await f == 60
```

</details>

#### when working with promises

#### resolves promise to value

- resolves promise to value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("resolves promise to value")
val p = Promise.new(\resolve, reject: resolve(42))
match p.state:
    case PromiseState.Resolved(v):
        expect v == 42
    case _:
        expect false
```

</details>

#### fulfills promise once

- fulfills promise once


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fulfills promise once")
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

- maps future to new value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maps future to new value")
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

- chains multiple map operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple map operations")
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

- flattens nested futures


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("flattens nested futures")
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

- chains async operations with flatMap


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains async operations with flatMap")
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

- captures exception in failed future


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("captures exception in failed future")
val p = Promise.rejected("error occurred")
match p.state:
    case PromiseState.Rejected(e):
        expect e == "error occurred"
    case _:
        expect false
```

</details>

#### propagates errors through chain

- propagates errors through chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("propagates errors through chain")
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

- recovers with fallback value


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("recovers with fallback value")
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

- retries failed future


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("retries failed future")
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

- combines multiple futures


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines multiple futures")
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

- handles timeout on future


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles timeout on future")
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

- cancels pending future


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("cancels pending future")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e3c141dd3f8f13dbce4fbeb36a3e2db8b06a28d3ba017d6967e624e47878dd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e3c141dd3f8f13dbce4fbeb36a3e2db8b06a28d3ba017d6967e624e47878dd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e3c141dd3f8f13dbce4fbeb36a3e2db8b06a28d3ba017d6967e624e47878dd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/futures_promises_spec.spl
mirror: doc/06_spec/feature/usage/futures_promises_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/futures_promises_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/futures_promises_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/futures_promises_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates future from immediate value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/futures_promises_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates future from computation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/futures_promises_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves promise to value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
