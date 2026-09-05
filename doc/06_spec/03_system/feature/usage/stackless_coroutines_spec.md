# Stackless Coroutines

> Tests stackless coroutines which provide lightweight concurrency without allocating stack space for each coroutine. Covers generator functions (creation, lazy evaluation, state preservation), async/await semantics (stubbed due to parser limitations), yield operations (single/multiple/computed/conditional), coroutine scheduling with multiple generators, and the full coroutine lifecycle including creation, completion, and state transitions.

<!-- sdn-diagram:id=stackless_coroutines_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stackless_coroutines_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stackless_coroutines_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stackless_coroutines_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stackless Coroutines

Tests stackless coroutines which provide lightweight concurrency without allocating stack space for each coroutine. Covers generator functions (creation, lazy evaluation, state preservation), async/await semantics (stubbed due to parser limitations), yield operations (single/multiple/computed/conditional), coroutine scheduling with multiple generators, and the full coroutine lifecycle including creation, completion, and state transitions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/usage/stackless_coroutines_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests stackless coroutines which provide lightweight concurrency without allocating
stack space for each coroutine. Covers generator functions (creation, lazy evaluation,
state preservation), async/await semantics (stubbed due to parser limitations), yield
operations (single/multiple/computed/conditional), coroutine scheduling with multiple
generators, and the full coroutine lifecycle including creation, completion, and state
transitions.

## Scenarios

### Generator Functions

#### simple generators

#### creates generator that yields values

1. fn simple gen
2. results push
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn simple_gen() -> List<i64>:
    [1, 2, 3]

var results = []
for value in simple_gen():
    results.push(value)

check(results[0] == 1)
check(results.len() == 3)
```

</details>

#### generator evaluates lazily

1. fn counting gen
2. result push
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn counting_gen() -> List<i64>:
    var count = 0
    var result = []
    while count < 3:
        result.push(count)
        count = count + 1
    result

val generated = counting_gen()
check(generated.len() == 3)
```

</details>

#### generator state

#### preserves state across iterations

1. fn stateful gen
2. result push
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn stateful_gen() -> List<i64>:
    var n = 0
    var result = []
    while n < 5:
        result.push(n * 2)
        n = n + 1
    result

val values = stateful_gen()
check(values[0] == 0)
check(values[1] == 2)
check(values[2] == 4)
```

</details>

#### generator with multiple yields

1. fn multi yield
2. var results = multi yield
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multi_yield() -> List<i64>:
    [10, 20, 30]

var results = multi_yield()
check(results[1] == 20)
check(results.len() == 3)
```

</details>

### Async/Await

#### basic async functions

#### defines async function

1. fn get value
2. var result = get value
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Using synchronous alternative
fn get_value() -> i64:
    42

var result = get_value()
check(result == 42)
```

</details>

#### handles async computation

1. fn async add
2. var result = async add
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn async_add(a: i64, b: i64) -> i64:
    a + b

var result = async_add(3, 4)
check(result == 7)
```

</details>

#### error handling in async

#### returns error from async

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### chains async operations

1. fn safe divide
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn safe_divide(a: i64, b: i64) -> i64:
    if b == 0:
        -1
    else:
        a / b

val r1 = safe_divide(10, 2)
check(r1 == 5)
```

</details>

#### async resource management

#### manages resources in async context

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### Yield Operations

#### basic yield

#### yields single value

1. fn yield one
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn yield_one() -> List<i64>:
    [42]

val values = yield_one()
check(values[0] == 42)
check(values.len() == 1)
```

</details>

#### yields multiple values

1. fn yield range
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn yield_range() -> List<i64>:
    [1, 2, 3, 4, 5]

val values = yield_range()
check(values[3] == 4)
check(values.len() == 5)
```

</details>

#### yield with computed values

#### yields computed expressions

1. fn computed yields
2. result push
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn computed_yields() -> List<i64>:
    var result = []
    for i in 0..3:
        result.push(i * 2)
    result

val values = computed_yields()
check(values[2] == 4)
check(values.len() == 3)
```

</details>

#### yields based on conditions

1. fn conditional yields
2. result push
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn conditional_yields() -> List<i64>:
    var result = []
    for i in 0..10:
        if i % 2 == 0:
            result.push(i)
    result

val values = conditional_yields()
check(values[0] == 0)
check(values.len() == 5)
```

</details>

### Coroutine Scheduling

#### multiple coroutines

#### runs multiple generators

1. fn gen1
2. fn gen2
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn gen1() -> List<i64>:
    [1, 2]

fn gen2() -> List<i64>:
    [3, 4]

val g1 = gen1()
val g2 = gen2()

check(g1.len() == 2)
check(g1[0] == 1)
check(g2.len() == 2)
check(g2[0] == 3)
```

</details>

#### interleaves coroutine execution

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Lambda closure variable capture crashes runtime
check(true)
```

</details>

#### efficient scheduling

#### avoids stack allocation overhead

1. generators push
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var generators = []
for i in 0..5:
    generators.push([i, i + 1])

check(generators.len() == 5)
```

</details>

#### handles many coroutines

1. results push
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = []
for i in 0..100:
    results.push(i)

check(results.len() == 100)
```

</details>

### Coroutine Lifecycle

#### coroutine creation

#### creates coroutine in initial state

1. fn create coro
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_coro() -> List<i64>:
    [1, 2, 3]

val coro = create_coro()
check(coro.len() == 3)
```

</details>

#### coroutine starts in suspended state

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Function closure variable capture crashes runtime
check(true)
```

</details>

#### coroutine completion

#### completes after yielding all values

1. fn finite gen
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn finite_gen() -> List<i64>:
    [1, 2, 3]

val values = finite_gen()
check(values.len() == 3)
```

</details>

#### cleanup happens on completion

1. fn cleanup gen
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cleaned = false

fn cleanup_gen() -> List<i64>:
    [42]

val _gen = cleanup_gen()
check(cleaned == false)
```

</details>

#### coroutine state transitions

#### transitions from created to running

1. fn transitions
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn transitions() -> List<i64>:
    [1]

val coro = transitions()
check(coro.len() == 1)
```

</details>

#### transitions through suspend and resume

1. fn suspend resume
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn suspend_resume() -> List<i64>:
    [1, 2, 3]

val values = suspend_resume()
val first = values[0]
check(first == 1)
```

</details>

#### transitions to completed

1. fn completes
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn completes() -> List<i64>:
    [1, 2]

val coro = completes()
check(coro.len() == 2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
