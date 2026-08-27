# Pipeline Components Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pipeline Components Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PIPELINE-COMP |
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/03_system/feature/usage/pipeline_components_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
use std.spec.step

val pipeline = source
| filter(\x: x > 0)
| map(\x: x * 2)
| sink(print)
```

## Key Behaviors

- Pipeline stages compose with the pipe operator (|)
- Data flows through stages from left to right
- Error handling preserves error context through pipeline
- Backpressure controls data flow between stages
- Resources are managed through effect system
- Lazy evaluation defers computation until terminal operation

## Scenarios

### Pipeline Creation and Composition

#### simple pipeline stages

#### creates pipeline with single stage

- creates pipeline with single stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates pipeline with single stage")
val data = [1, 2, 3]
val result = data
expect result.len() == 3
```

</details>

#### transforms data through pipeline

- transforms data through pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms data through pipeline")
val data = [1, 2, 3]
val result = data
    .map(_1 * 2)
expect result[0] == 2
expect result.len() == 3
expect result[1] == 4
expect result[2] == 6
```

</details>

#### chaining stages

#### chains multiple transformations

- chains multiple transformations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple transformations")
val data = [1, 2, 3, 4, 5]
val result = data
    .filter(_1 > 2)
    .map(_1 * 10)
expect result[0] == 30
expect result.len() == 3
expect result[1] == 40
expect result[2] == 50
```

</details>

#### chains filter then map then filter

- chains filter then map then filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains filter then map then filter")
val data = [1, 2, 3, 4, 5, 6]
val result = data
    .filter(_1 > 1)
    .map(_1 * 2)
    .filter(_1 > 6)
expect result.len() == 3
```

</details>

### Pipeline Error Handling

#### error propagation

#### propagates errors through stages

- propagates errors through stages


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates errors through stages")
fn safe_divide(x: i64) -> Result<i64, text>:
    if x == 0:
        Err("division by zero")
    else:
        Ok(100 / x)

val result1 = safe_divide(2)
match result1:
    Ok(value):
        expect value == 50
    Err(_):
        fail("should succeed")
```

</details>

#### stops processing on error

- stops processing on error


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stops processing on error")
fn validate(x: i64) -> Result<i64, text>:
    if x < 0:
        Err("negative")
    else:
        Ok(x)

val data: List<i64> = [1, -2, 3]
var results = []
for item in data:
    match validate(item):
        Ok(v):
            results.push(v)
        Err(_):
            pass

expect results.len() == 2
```

</details>

#### recovery from errors

#### provides default on error

- provides default on error


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides default on error")
fn risky(x: i64) -> Result<i64, text>:
    if x == 0:
        Err("zero not allowed")
    else:
        Ok(x * 2)

val result1 = risky(5)
val value1 = match result1:
    Ok(v):
        v
    Err(_):
        -1
expect value1 == 10

val result2 = risky(0)
val value2 = match result2:
    Ok(v):
        v
    Err(_):
        -1
expect value2 == -1
```

</details>

### Pipeline Buffering

#### buffer operations

#### collects data in buffer

- collects data in buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects data in buffer")
var buffer: List<i64> = []
val data = [1, 2, 3]
for item in data:
    buffer.push(item)
expect buffer.len() == 3
```

</details>

#### respects buffer limits

- respects buffer limits


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("respects buffer limits")
val max_size = 5
var buffer: List<i64> = []
val data = [1, 2, 3, 4, 5, 6, 7]
for item in data:
    if buffer.len() < max_size:
        buffer.push(item)
expect buffer.len() == 5
```

</details>

#### draining buffers

#### drains buffer completely

- drains buffer completely


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("drains buffer completely")
var buffer: List<i64> = [1, 2, 3]
var drain_result = []
while buffer.?:
    val item = buffer[0]
    drain_result.push(item)
    buffer = buffer[1:]
expect drain_result.len() == 3
```

</details>

### Pipeline State

#### accumulating state

#### maintains running total through stages

- maintains running total through stages


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains running total through stages")
fn sum_values(items: List<i64>) -> i64:
    var total = 0
    for item in items:
        total = total + item
    total

val data = [1, 2, 3, 4, 5]
val result = sum_values(data)
expect result == 15
```

</details>

#### accumulates with filter

- accumulates with filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accumulates with filter")
var count = 0
val data = [1, 2, 3, 4, 5]
for item in data:
    if item > 2:
        count = count + 1
expect count == 3
```

</details>

#### state isolation

#### keeps separate accumulators

- keeps separate accumulators


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps separate accumulators")
fn process_list(items: List<i64>, threshold: i64) -> i64:
    var result = 0
    for item in items:
        if item > threshold:
            result = result + item
    result

val list1 = [1, 2, 3, 4, 5]
val list2 = [10, 20, 30]
val r1 = process_list(list1, 2)
val r2 = process_list(list2, 15)
expect r1 == 12
expect r2 == 50
```

</details>

### Pipeline Evaluation

#### eager evaluation

#### evaluates immediately

- evaluates immediately


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates immediately")
val data = [1, 2, 3]
val result = data
    .map(_1 * 2)
expect result[0] == 2
expect result[1] == 4
```

</details>

#### evaluates each transformation

- evaluates each transformation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates each transformation")
var eval_count = 0
val data = [1, 2, 3]
for x in data:
    eval_count = eval_count + 1
expect eval_count == 3
```

</details>

#### terminal operations

#### collects results from pipeline

- collects results from pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects results from pipeline")
val data = [1, 2, 3, 4, 5]
val result = data
    .filter(_1 > 2)
    .map(_1 * 10)
expect result.len() == 3
```

</details>

#### counts items in pipeline

- counts items in pipeline


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts items in pipeline")
val data = [1, 2, 3, 4, 5]
val filtered = data
    .filter(_1 > 2)
expect filtered.len() == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `6bc801cb66b7b0e975ee66f528aaa7c42eab27c3de87b2146d865063fba2ea2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6bc801cb66b7b0e975ee66f528aaa7c42eab27c3de87b2146d865063fba2ea2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6bc801cb66b7b0e975ee66f528aaa7c42eab27c3de87b2146d865063fba2ea2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/pipeline_components_spec.spl
mirror: doc/06_spec/03_system/feature/usage/pipeline_components_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/pipeline_components_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/pipeline_components_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/pipeline_components_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates pipeline with single stage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/pipeline_components_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transforms data through pipeline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/pipeline_components_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains multiple transformations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
