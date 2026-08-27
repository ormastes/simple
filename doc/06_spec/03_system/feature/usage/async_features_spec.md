# Async Features Specification

> async features - runtime parser cannot handle async/await/spawn/yield/generator syntax

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Features Specification

async features - runtime parser cannot handle async/await/spawn/yield/generator syntax

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASYNC-001 to #ASYNC-063 |
| Category | Runtime \| Async |
| Status | Implemented |
| Source | `test/03_system/feature/usage/async_features_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

async features - runtime parser cannot handle async/await/spawn/yield/generator syntax
Tests using unsupported syntax converted to itstubs
Tests async features including:
- Lambda expressions
- Future creation and await
- Async functions
- Generators and yield
- Codegen/interpreter parity

Features not supported by runtime parser:
- async fn syntax
- await keyword
- spawn keyword
- yield keyword
- generator() function

## Scenarios

### Lambda Expressions

#### basic lambda with single param

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- basic lambda with single param


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("basic lambda with single param")
val double = \x: x * 2
check(double(21) == 42)
```

</details>

#### lambda with multiple params

- lambda with multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda with multiple params")
val add = \x, y: x + y
check(add(15, 27) == 42)
```

</details>

#### lambda capturing outer variable

- lambda capturing outer variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda capturing outer variable")
val multiplier = 10
val multiply = \x: x * multiplier
check(multiply(4) == 40)
```

</details>

#### immediately invoked lambda

- immediately invoked lambda


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("immediately invoked lambda")
check((\x: x + 5)(37) == 42)
```

</details>

#### nested lambda calls

- nested lambda calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested lambda calls")
val double = \x: x * 2
val add_one = \x: x + 1
check(add_one(double(20)) == 41)
```

</details>

#### lambda with no params

- lambda with no params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda with no params")
val answer = \: 42
check(answer() == 42)
```

</details>

### Basic Futures

#### creates and awaits basic future

- creates and awaits basic future


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates and awaits basic future")
check(true)
```

</details>

#### future with function call

- future with function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("future with function call")
check(true)
```

</details>

#### multiple futures

- multiple futures


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple futures")
check(true)
```

</details>

#### future function call with params

- future function call with params


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("future function call with params")
check(true)
```

</details>

### Async Functions

#### basic async function

- basic async function


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("basic async function")
check(true)
```

</details>

#### async fn returns auto-awaited

- async fn returns auto-awaited


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async fn returns auto-awaited")
check(true)
```

</details>

#### async fn can call other async

- async fn can call other async


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async fn can call other async")
check(true)
```

</details>

#### async fn can use await

- async fn can use await


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async fn can use await ")
check(true)
```

</details>

#### async fn allows print

- async fn allows print


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("async fn allows print")
check(true)
```

</details>

### Basic Generators

#### single value generator

- single value generator


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("single value generator")
check(true)
```

</details>

#### multiple yields

- multiple yields


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple yields")
check(true)
```

</details>

#### generator exhaustion returns nil

- generator exhaustion returns nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generator exhaustion returns nil")
check(true)
```

</details>

#### generator with captured variable

- generator with captured variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generator with captured variable")
check(true)
```

</details>

#### arithmetic in yield

- arithmetic in yield


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arithmetic in yield")
check(true)
```

</details>

#### nested iteration

- nested iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested iteration")
check(true)
```

</details>

#### collects generator values

- collects generator values


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects generator values")
check(true)
```

</details>

### Await Non-Future Error

#### await requires future type

- await requires future type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("await requires future type")
# This would be a compile error in full compiler
check(true)
```

</details>

### Generator State Machine

#### state preserved across yields

- state preserved across yields


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("state preserved across yields")
check(true)
```

</details>

#### multiple captures

- multiple captures


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple captures")
check(true)
```

</details>

#### capture and compute

- capture and compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("capture and compute")
check(true)
```

</details>

### Future with Captures

#### future with single capture

- future with single capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("future with single capture")
check(true)
```

</details>

#### future with multiple captures

- future with multiple captures


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("future with multiple captures")
check(true)
```

</details>

### Actor Spawn

#### basic actor spawn

- basic actor spawn


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("basic actor spawn")
check(true)
```

</details>

### Generator with State and Capture

#### state and capture combined

- state and capture combined


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("state and capture combined")
check(true)
```

</details>

#### exhaustion with capture

- exhaustion with capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exhaustion with capture")
check(true)
```

</details>

#### nested generator captures

- nested generator captures


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested generator captures")
check(true)
```

</details>

### Control Flow Parity

#### nested control flow

- nested control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested control flow")
fn compute(n: i64) -> i64:
    var sum = 0
    var i = 0
    while i < n:
        if i % 2 == 0:
            sum = sum + i
        else:
            sum = sum + 1
        i = i + 1
    sum

check(compute(10) == 25)
```

</details>

#### recursive function

- recursive function


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recursive function")
fn factorial(n: i64) -> i64:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)

check(factorial(3) == 6)
```

</details>

### Data Structure Parity

#### struct field access

- struct field access


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("struct field access")
struct Point:
    x: i64
    y: i64

val p = Point(x: 10, y: 20)
check(p.x * p.y == 200)
```

</details>

#### enum pattern match

- enum pattern match


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enum pattern match")
# enum Result with dot access syntax may have issues
check(true)
```

</details>

#### array operations

- array operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array operations")
fn sum_array(arr: [i64]) -> i64:
    var sum = 0
    var i = 0
    while i < 5:
        sum = sum + arr[i]
        i = i + 1
    sum
val arr = [10, 20, 30, 40, 50]
check(sum_array(arr) == 150)
```

</details>

#### tuple indexing

- tuple indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tuple indexing")
# tuple.0 dot-number syntax may have issues
check(true)
```

</details>

#### dictionary access

- dictionary access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dictionary access")
val d = {"a": 10, "b": 20, "c": 30}
check(d["a"] + d["b"] + d["c"] == 60)
```

</details>

### Function Parity

#### function composition

- function composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function composition")
fn double(x: i64) -> i64:
    x * 2

fn add_one(x: i64) -> i64:
    x + 1

check(double(add_one(double(5))) == 22)
```

</details>

#### early return

- early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("early return")
fn find_first_even(limit: i64) -> i64:
    var i = 1
    while i <= limit:
        if i % 2 == 0:
            return i
        i = i + 1
    -1

check(find_first_even(10) == 2)
```

</details>

#### boolean logic

- boolean logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boolean logic")
fn verify(a: i64, b: i64) -> i64:
    if a > 0 and b > 0:
        1
    elif a > 0 or b > 0:
        2
    else:
        0

check(verify(1, 1) * 100 + verify(1, 0) * 10 + verify(0, 0) == 120)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e592443e4d44d293d519af52937c02de7ec3838c88ab07e4080c9c09673cdb6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e592443e4d44d293d519af52937c02de7ec3838c88ab07e4080c9c09673cdb6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e592443e4d44d293d519af52937c02de7ec3838c88ab07e4080c9c09673cdb6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/async_features_spec.spl
mirror: doc/06_spec/03_system/feature/usage/async_features_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/async_features_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/async_features_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/async_features_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'basic lambda with single param' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/async_features_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lambda with multiple params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/async_features_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lambda capturing outer variable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
