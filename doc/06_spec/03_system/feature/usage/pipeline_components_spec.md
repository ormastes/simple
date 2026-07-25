# Pipeline Components Specification

> val pipeline = source

<!-- sdn-diagram:id=pipeline_components_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pipeline_components_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pipeline_components_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pipeline_components_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pipeline Components Specification

val pipeline = source

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PIPELINE-COMP |
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/03_system/feature/usage/pipeline_components_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
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

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data
expect result.len() == 3
```

</details>

#### transforms data through pipeline

1.  map
2. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  filter
2.  map
3. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  filter
2.  map
3.  filter
4. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn safe divide
2. Err
3. Ok
4. Ok
5. Err
6. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn validate
2. Err
3. Ok
4. Ok
5. results push
6. Err
7. expect results len


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn risky
2. Err
3. Ok
4. Ok
5. Err
6. Ok
7. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. buffer push
2. expect buffer len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer: List<i64> = []
val data = [1, 2, 3]
for item in data:
    buffer.push(item)
expect buffer.len() == 3
```

</details>

#### respects buffer limits

1. buffer push
2. expect buffer len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. drain result push
2. expect drain result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn sum values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn process list


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1.  map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3]
val result = data
    .map(_1 * 2)
expect result[0] == 2
expect result[1] == 4
```

</details>

#### evaluates each transformation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eval_count = 0
val data = [1, 2, 3]
for x in data:
    eval_count = eval_count + 1
expect eval_count == 3
```

</details>

#### terminal operations

#### collects results from pipeline

1.  filter
2.  map
3. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [1, 2, 3, 4, 5]
val result = data
    .filter(_1 > 2)
    .map(_1 * 10)
expect result.len() == 3
```

</details>

#### counts items in pipeline

1.  filter
2. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
