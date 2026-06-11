# Promise Specification

> 1. expect p is resolved

<!-- sdn-diagram:id=promise_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=promise_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

promise_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=promise_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Promise Specification

## Scenarios

### Promise<T> - Basic Operations

#### creates a resolved promise

1. expect p is resolved
2. expect not p is pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_resolved(42)
expect p.is_resolved()
expect not p.is_pending()
```

</details>

#### creates a rejected promise

1. expect p is rejected
2. expect not p is pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_rejected("error")
expect p.is_rejected()
expect not p.is_pending()
```

</details>

#### creates a promise with executor that resolves

1. expect p is resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.new(\resolve, reject: resolve(100))
expect p.is_resolved()
```

</details>

#### creates a promise with executor that rejects

1. expect p is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.new(\resolve, reject: reject("failed"))
expect p.is_rejected()
```

</details>

#### starts as pending before executor runs

1. expect p is pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For immediate executors, promise resolves synchronously
# This tests the initial state construction
val p = Promise {
    state: PromiseState.Pending,
    callbacks: []
}
expect p.is_pending()
```

</details>

### Promise<T> - State Management

#### resolves only once

1. resolve
2. resolve
3. expect p is resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolve_count = 0
val p = Promise.new(\resolve, reject:
    resolve(1)
    resolve(2)  # Should be ignored
)
expect p.is_resolved()
# Verify first value was used (can't check exact value without await)
```

</details>

#### rejects only once

1. reject
2. reject
3. expect p is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reject_count = 0
val p = Promise.new(\resolve, reject:
    reject("first")
    reject("second")  # Should be ignored
)
expect p.is_rejected()
```

</details>

#### cannot transition from resolved to rejected

1. resolve
2. reject
3. expect p is resolved
4. expect not p is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.new(\resolve, reject:
    resolve(42)
    reject("error")  # Should be ignored
)
expect p.is_resolved()
expect not p.is_rejected()
```

</details>

#### cannot transition from rejected to resolved

1. reject
2. resolve
3. expect p is rejected
4. expect not p is resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise.new(\resolve, reject:
    reject("error")
    resolve(42)  # Should be ignored
)
expect p.is_rejected()
expect not p.is_resolved()
```

</details>

#### preserves state after creation

1. expect p1 is resolved
2. expect p2 is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = make_resolved(10)
val p2 = make_rejected("err")

# Check states are stable
expect p1.is_resolved()
expect p2.is_rejected()
```

</details>

### Promise<T> - Type Safety

#### can hold integer values

1. expect p is resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_resolved(42)
expect p.is_resolved()
```

</details>

#### can hold string values

1. expect p is resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_resolved("hello")
expect p.is_resolved()
```

</details>

#### can hold errors as strings

1. expect p is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_rejected("error message")
expect p.is_rejected()
```

</details>

### Promise<T> - Edge Cases

#### handles nil resolution

1. expect p is resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_resolved(nil)
expect p.is_resolved()
```

</details>

#### handles nil rejection

1. expect p is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_rejected(nil)
expect p.is_rejected()
```

</details>

#### handles empty callback list

1. state: PromiseState Resolved
2. expect p is resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Promise {
    state: PromiseState.Resolved(42),
    callbacks: []
}
expect p.is_resolved()
```

</details>

### Promise<T> - Integration

#### works with match expressions on state

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_resolved(100)
var matched = false

match p.state:
    case PromiseState.Resolved(v):
        matched = true
    case _:
        matched = false

expect matched
```

</details>

#### works with match expressions for rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_rejected("error")
var matched = false

match p.state:
    case PromiseState.Rejected(e):
        matched = true
    case _:
        matched = false

expect matched
```

</details>

#### executor receives both callbacks

1. resolve
2. reject


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resolve_called = false
var reject_called = false

val p1 = Promise.new(\resolve, reject:
    resolve_called = true
    resolve(1)
)

val p2 = Promise.new(\resolve, reject:
    reject_called = true
    reject("err")
)

expect resolve_called
expect reject_called
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/promise_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Promise<T> - Basic Operations
- Promise<T> - State Management
- Promise<T> - Type Safety
- Promise<T> - Edge Cases
- Promise<T> - Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
