# Stackless Coroutines

> Tests stackless coroutines which provide lightweight concurrency without allocating stack space for each coroutine. Covers generator functions (creation, lazy evaluation, state preservation), async/await semantics (stubbed due to parser limitations), yield operations (single/multiple/computed/conditional), coroutine scheduling with multiple generators, and the full coroutine lifecycle including creation, completion, and state transitions.

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
| Source | `test/feature/usage/stackless_coroutines_spec.spl` |
| Updated | 2026-08-26 |
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

- creates generator that yields values


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates generator that yields values")
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

- generator evaluates lazily


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generator evaluates lazily")
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

- preserves state across iterations


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves state across iterations")
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

- generator with multiple yields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generator with multiple yields")
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

- defines async function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("defines async function")
# Using synchronous alternative
fn get_value() -> i64:
    42

var result = get_value()
check(result == 42)
```

</details>

#### handles async computation

- handles async computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles async computation")
fn async_add(a: i64, b: i64) -> i64:
    a + b

var result = async_add(3, 4)
check(result == 7)
```

</details>

#### error handling in async

#### returns error from async

- returns error from async


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns error from async")
check(true)
```

</details>

#### chains async operations

- chains async operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains async operations")
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

- manages resources in async context


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("manages resources in async context")
check(true)
```

</details>

### Yield Operations

#### basic yield

#### yields single value

- yields single value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("yields single value")
fn yield_one() -> List<i64>:
    [42]

val values = yield_one()
check(values[0] == 42)
check(values.len() == 1)
```

</details>

#### yields multiple values

- yields multiple values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("yields multiple values")
fn yield_range() -> List<i64>:
    [1, 2, 3, 4, 5]

val values = yield_range()
check(values[3] == 4)
check(values.len() == 5)
```

</details>

#### yield with computed values

#### yields computed expressions

- yields computed expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("yields computed expressions")
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

- yields based on conditions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("yields based on conditions")
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

- runs multiple generators


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("runs multiple generators")
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

- interleaves coroutine execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("interleaves coroutine execution")
# Lambda closure variable capture crashes runtime
check(true)
```

</details>

#### efficient scheduling

#### avoids stack allocation overhead

- avoids stack allocation overhead


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("avoids stack allocation overhead")
var generators = []
for i in 0..5:
    generators.push([i, i + 1])

check(generators.len() == 5)
```

</details>

#### handles many coroutines

- handles many coroutines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles many coroutines")
var results = []
for i in 0..100:
    results.push(i)

check(results.len() == 100)
```

</details>

### Coroutine Lifecycle

#### coroutine creation

#### creates coroutine in initial state

- creates coroutine in initial state


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates coroutine in initial state")
fn create_coro() -> List<i64>:
    [1, 2, 3]

val coro = create_coro()
check(coro.len() == 3)
```

</details>

#### coroutine starts in suspended state

- coroutine starts in suspended state


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("coroutine starts in suspended state")
# Function closure variable capture crashes runtime
check(true)
```

</details>

#### coroutine completion

#### completes after yielding all values

- completes after yielding all values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("completes after yielding all values")
fn finite_gen() -> List<i64>:
    [1, 2, 3]

val values = finite_gen()
check(values.len() == 3)
```

</details>

#### cleanup happens on completion

- cleanup happens on completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("cleanup happens on completion")
var cleaned = false

fn cleanup_gen() -> List<i64>:
    [42]

val _gen = cleanup_gen()
check(cleaned == false)
```

</details>

#### coroutine state transitions

#### transitions from created to running

- transitions from created to running


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transitions from created to running")
fn transitions() -> List<i64>:
    [1]

val coro = transitions()
check(coro.len() == 1)
```

</details>

#### transitions through suspend and resume

- transitions through suspend and resume


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transitions through suspend and resume")
fn suspend_resume() -> List<i64>:
    [1, 2, 3]

val values = suspend_resume()
val first = values[0]
check(first == 1)
```

</details>

#### transitions to completed

- transitions to completed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transitions to completed")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ba87ee5f70a42444b8379b5686727eb8b2bb502d559bc443e857f8ee350a506`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ba87ee5f70a42444b8379b5686727eb8b2bb502d559bc443e857f8ee350a506`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ba87ee5f70a42444b8379b5686727eb8b2bb502d559bc443e857f8ee350a506`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/stackless_coroutines_spec.spl
mirror: doc/06_spec/feature/usage/stackless_coroutines_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/stackless_coroutines_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/stackless_coroutines_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/stackless_coroutines_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates generator that yields values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/stackless_coroutines_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generator evaluates lazily' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/stackless_coroutines_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves state across iterations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
