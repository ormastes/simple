# Integration & E2E Test

> 1. check

<!-- sdn-diagram:id=error_report_integration_1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_report_integration_1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_report_integration_1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_report_integration_1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration & E2E Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTEGRATION |
| Category | End-to-End Testing |
| Status | Implemented |
| Source | `test/02_integration/e2e/error_report_integration_1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Integration Test Scenario

#### e2e workflow 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = "source code"
val stage1 = input + " -> parsed"
val stage2 = stage1 + " -> typed"
val stage3 = stage2 + " -> compiled"
check(stage3.contains("compiled"))
```

</details>

#### e2e workflow 2

1. processed = processed append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val data = [1, 2, 3, 4, 5]
var processed = []
for x in data:
    processed = processed.append(x * 2)
var sum = 0
for x in processed:
    sum = sum + x
check(sum == 30)
```

</details>

#### e2e workflow 3

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val config = {"input": "test.spl", "output": "test.out"}
val input_file = config["input"]
val output_file = config["output"]
check(input_file.ends_with(".spl"))
check(output_file.ends_with(".out"))
```

</details>

#### error propagation

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var error = nil
if error == nil:
    check(true)
else:
    check(false)
```

</details>

#### state transitions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var state = "init"
if state == "init":
    state = "processing"
if state == "processing":
    state = "complete"
check(state == "complete")
```

</details>

#### data pipeline

1. filtered = filtered append
2. transformed = transformed append
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val raw = [1, 2, 3, 4, 5]
var filtered = []
for x in raw:
    if x % 2 == 0:
        filtered = filtered.append(x)
var transformed = []
for x in filtered:
    transformed = transformed.append(x * 10)
check(transformed.len() == 2)
```

</details>

#### module interaction

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val module_a = {"export": "value_a"}
val module_b = {"import": module_a["export"]}
check(module_b["import"] == "value_a")
```

</details>

#### nested processing

1. flattened = flattened append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val outer = [[1, 2], [3, 4], [5, 6]]
var flattened = []
for inner in outer:
    for x in inner:
        flattened = flattened.append(x)
check(flattened.len() == 6)
```

</details>

#### error recovery flow

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = nil
val result = opt ?? "default"
check(result == "default")
```

</details>

#### full validation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val input = [1, 2, 3, 4, 5]
var validated = true
for x in input:
    if x <= 0:
        validated = false
check(validated)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
