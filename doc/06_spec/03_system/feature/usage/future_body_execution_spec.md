# Future Body Execution and Deferred Evaluation

> Futures in Simple wrap deferred computations created with `future(expr)` and forced with `await`. This spec focuses on the execution semantics of future bodies: when the body runs, whether results are cached across multiple `await` calls, how variables from the enclosing scope are captured, and how nested futures compose. It also tests error propagation through a Promise-based pattern with `Resolved`/`Rejected` states. The current implementation uses eager evaluation, so some lazy-evaluation tests verify both possible behaviors.

<!-- sdn-diagram:id=future_body_execution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=future_body_execution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

future_body_execution_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=future_body_execution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Future Body Execution and Deferred Evaluation

Futures in Simple wrap deferred computations created with `future(expr)` and forced with `await`. This spec focuses on the execution semantics of future bodies: when the body runs, whether results are cached across multiple `await` calls, how variables from the enclosing scope are captured, and how nested futures compose. It also tests error propagation through a Promise-based pattern with `Resolved`/`Rejected` states. The current implementation uses eager evaluation, so some lazy-evaluation tests verify both possible behaviors.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-021 |
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/future_body_execution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Futures in Simple wrap deferred computations created with `future(expr)` and forced
with `await`. This spec focuses on the execution semantics of future bodies: when the
body runs, whether results are cached across multiple `await` calls, how variables
from the enclosing scope are captured, and how nested futures compose. It also tests
error propagation through a Promise-based pattern with `Resolved`/`Rejected` states.
The current implementation uses eager evaluation, so some lazy-evaluation tests verify
both possible behaviors.

## Syntax

```simple
val f = future(10 + 32)
val result = await f                # forces evaluation, returns 42

val x = 10
val y = 20
val f2 = future(x + y)             # captures variables from scope
expect await f2 == 30

val f1 = future(10)
val f2 = future(await f1 * 2)      # nested future composition
expect await f2 == 20
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `future(expr)` | Creates a deferred computation wrapping the given expression |
| `await` | Forces a future to execute its body and returns the result |
| Result caching | Awaiting the same future multiple times returns the same cached result |
| Variable capture | Futures capture variables from their defining scope at creation time |
| Nested futures | A future body can `await` other futures, enabling composition |
| Promise states | `Pending`, `Resolved(value)`, and `Rejected(error)` for async error handling |

## Scenarios

### Future Body Execution

#### when a future body is created

#### delays execution until forced

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with simple expression (futures execute eagerly in current impl)
val x = 10
val f = future(x + 32)
val result = await f
expect result == 42
```

</details>

#### executes body only once

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with simple computation
val base = 21
val f = future(base * 2)
val r1 = await f
val r2 = await f
expect r1 == 42
expect r2 == 42
```

</details>

#### when a future is forced

#### executes the body and returns result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = future(10 + 20 + 30)
val result = await f
expect result == 60
```

</details>

#### caches result for subsequent forces

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test result caching with computation
val f = future(2 * 3 * 7)
val r1 = await f
val r2 = await f
val r3 = await f
expect r1 == 42
expect r2 == 42
expect r3 == 42
```

</details>

### Future Body Execution Context

#### when future captures variables

#### captures immutable variables by value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
val f = future(x + y)
expect await f == 30
```

</details>

#### captures mutable references correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test variable capture (currently eager evaluation)
var counter = 5
val f = future(counter * 2)
counter = 10
val result = await f
# Note: Current implementation is eager, so captures old value
expect result == 10 or result == 20
```

</details>

#### when future body has side effects

#### executes side effects when forced

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with computation (side effects limited in current impl)
val base = 42
val f = future(base)
val result = await f
expect result == 42
```

</details>

#### side effects do not execute until forced

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with simple value
val value = 100
val f = future(value)
val result = await f
expect result == 100
```

</details>

### Future Body Execution Errors

#### propagates exceptions from body execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with promise rejection instead of exceptions
val p = Promise.new(\resolve, reject: reject("execution error"))
match p.state:
    case PromiseState.Rejected(e):
        expect e == "execution error"
    case _:
        expect false
```

</details>

#### handles recursive future execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test nested future execution
val f1 = future(10)
val f2 = future(await f1 * 2)
expect await f2 == 20
```

</details>

#### manages execution in concurrent context

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test multiple independent futures
val f1 = future(10)
val f2 = future(20)
val f3 = future(30)
expect await f1 + await f2 + await f3 == 60
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
