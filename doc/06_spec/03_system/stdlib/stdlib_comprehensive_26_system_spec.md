# Comprehensive System Test

> <details>

<!-- sdn-diagram:id=stdlib_comprehensive_26_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stdlib_comprehensive_26_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stdlib_comprehensive_26_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stdlib_comprehensive_26_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comprehensive System Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPREHENSIVE |
| Category | Testing |
| Status | Implemented |
| Source | `test/03_system/stdlib/stdlib_comprehensive_26_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Comprehensive System Test

<details>
<summary>Advanced: complete workflow 1</summary>

#### complete workflow 1 _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Input processing
val input = "test data"
verify(input.len() > 0)

# Transformation
val transformed = input + " processed"
verify(transformed.contains("processed"))

# Validation
val valid = transformed.len() > input.len()
verify(valid)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 2</summary>

#### complete workflow 2 _(slow)_

1. items = items append
2. verify
3. evens = evens append
4. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Collection processing
var items = []
for i in 0..20:
    items = items.append(i * 2)

verify(items.len() == 20)

# Filter
var evens = []
for item in items:
    if item % 4 == 0:
        evens = evens.append(item)

verify(evens.len() == 10)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 3</summary>

#### complete workflow 3 _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# String manipulation pipeline
val text = "Hello World"
val lower = text  # Simulated lowercase
val parts = lower.split(" ")
verify(parts.len() == 2)

val rejoined = parts.join("-")
verify(rejoined.contains("-"))
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 4</summary>

#### complete workflow 4 _(slow)_

1. row data = row data append
2. matrix = matrix append
3. verify
4. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Nested data structures
var matrix = []
for row in 0..5:
    var row_data = []
    for col in 0..5:
        row_data = row_data.append(row * 5 + col)
    matrix = matrix.append(row_data)

verify(matrix.len() == 5)
verify(matrix[0].len() == 5)
```

</details>


</details>

<details>
<summary>Advanced: complete workflow 5</summary>

#### complete workflow 5 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Option handling pipeline
val opt1 = Some(10)
val opt2 = Some(20)

var result = 0
if opt1.? and opt2.?:
    result = opt1? + opt2?

verify(result == 30)
```

</details>


</details>

<details>
<summary>Advanced: error recovery 1</summary>

#### error recovery 1 _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error = nil

# Simulate operation that might fail
val risky_value = Some(42)
if risky_value.?:
    verify(true)
else:
    error = "Failed"

verify(error == nil)
```

</details>


</details>

<details>
<summary>Advanced: error recovery 2</summary>

#### error recovery 2 _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Graceful degradation
val primary = nil
val fallback = Some(99)

val result = primary ?? fallback
verify(result.?)
verify(result? == 99)
```

</details>


</details>

<details>
<summary>Advanced: stress test 1</summary>

#### stress test 1 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for i in 0..100:
    total = total + i
verify(total == 4950)
```

</details>


</details>

<details>
<summary>Advanced: stress test 2</summary>

#### stress test 2 _(slow)_

1. data = data append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = []
for i in 0..50:
    data = data.append("item_{i}")
verify(data.len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: stress test 3</summary>

#### stress test 3 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nested_count = 0
for i in 0..10:
    for j in 0..10:
        nested_count = nested_count + 1
verify(nested_count == 100)
```

</details>


</details>

<details>
<summary>Advanced: boundary test 1</summary>

#### boundary test 1 _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = 0
val one = 1
val negative = -1

verify(zero == 0)
verify(one > zero)
verify(negative < zero)
```

</details>


</details>

<details>
<summary>Advanced: boundary test 2</summary>

#### boundary test 2 _(slow)_

1. verify
2. verify
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = []
val single = [1]
val double = [1, 2]

verify(empty.len() == 0)
verify(single.len() == 1)
verify(double.len() == 2)
```

</details>


</details>

<details>
<summary>Advanced: integration test 1</summary>

#### integration test 1 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multi-step processing
val step1 = "input"
val step2 = step1 + "_s2"
val step3 = step2 + "_s3"
val step4 = step3 + "_s4"

verify(step4 == "input_s2_s3_s4")
```

</details>


</details>

<details>
<summary>Advanced: integration test 2</summary>

#### integration test 2 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pipeline with branching
val value = 15

var result = "large"
if value > 10:
    if value < 20:
        result = "medium"

verify(result == "medium")
```

</details>


</details>

<details>
<summary>Advanced: regression test 1</summary>

#### regression test 1 _(slow)_

1. verify
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ensure old behavior still works
val arr = [1, 2, 3]
val first = arr[0]
val last = arr[-1]

verify(first == 1)
verify(last == 3)
```

</details>


</details>

<details>
<summary>Advanced: regression test 2</summary>

#### regression test 2 _(slow)_

1. verify
2. verify
3. verify
4. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# String operations stability
val s = "test"
verify(s.len() == 4)
verify(s.contains("es"))
verify(s.starts_with("te"))
verify(s.ends_with("st"))
```

</details>


</details>

<details>
<summary>Advanced: performance test 1</summary>

#### performance test 1 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Many iterations
var count = 0
for i in 0..200:
    count = count + 1
verify(count == 200)
```

</details>


</details>

<details>
<summary>Advanced: performance test 2</summary>

#### performance test 2 _(slow)_

1. large = large append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Large collection
var large = []
for i in 0..100:
    large = large.append(i)
verify(large.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: concurrency simulation 1</summary>

#### concurrency simulation 1 _(slow)_

1. ops = ops append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple operations
var ops = []
for i in 0..30:
    ops = ops.append({"id": i, "status": "done"})
verify(ops.len() == 30)
```

</details>


</details>

<details>
<summary>Advanced: concurrency simulation 2</summary>

#### concurrency simulation 2 _(slow)_

1. results = results append
2. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Parallel-style processing
var results = []
for i in [1, 2, 3, 4, 5]:
    results = results.append(i * i)
verify(results.len() == 5)
```

</details>


</details>

<details>
<summary>Advanced: resource management 1</summary>

#### resource management 1 _(slow)_

1. allocated = allocated append
2. var freed = allocated len
3. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Allocation tracking
var allocated = []
for i in 0..20:
    allocated = allocated.append(i)

# Simulated cleanup
var freed = allocated.len()
verify(freed == 20)
```

</details>


</details>

<details>
<summary>Advanced: complex logic 1</summary>

#### complex logic 1 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = 30

var result = "unequal spacing"
if a < b and b < c:
    if c - b == b - a:
        result = "equal spacing"

verify(result == "equal spacing")
```

</details>


</details>

<details>
<summary>Advanced: complex logic 2</summary>

#### complex logic 2 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "initial"

state = "last"

verify(state == "last")
```

</details>


</details>

<details>
<summary>Advanced: data validation 1</summary>

#### data validation 1 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"name": "test", "value": 42}

val valid = data.get("name").? and data.get("value").?
verify(valid)
```

</details>


</details>

<details>
<summary>Advanced: data validation 2</summary>

#### data validation 2 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]

var all_positive = true
for item in items:
    if item <= 0:
        all_positive = false
        break

verify(all_positive)
```

</details>


</details>

<details>
<summary>Advanced: state machine 1</summary>

#### state machine 1 _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "start"

if state == "start":
    state = "processing"

if state == "processing":
    state = "done"

verify(state == "done")
```

</details>


</details>

<details>
<summary>Advanced: cleanup verification</summary>

#### cleanup verification _(slow)_

1. verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = [1, 2, 3, 4, 5]
var cleaned = 0

for r in resources:
    cleaned = cleaned + 1

verify(cleaned == resources.len())
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 27 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
