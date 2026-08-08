# Integration & E2E Test

> <details>

<!-- sdn-diagram:id=lexer_parser_integration_6_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lexer_parser_integration_6_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lexer_parser_integration_6_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lexer_parser_integration_6_spec.arch hash=sha256:auto
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
| Source | `test/02_integration/e2e/lexer_parser_integration_6_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Integration Test Scenario

<details>
<summary>Advanced: e2e workflow 1</summary>

#### e2e workflow 1 _(slow)_

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


</details>

<details>
<summary>Advanced: e2e workflow 2</summary>

#### e2e workflow 2 _(slow)_

1. processed = processed append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: e2e workflow 3</summary>

#### e2e workflow 3 _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = {"input": "test.spl", "output": "test.out"}
val input_file = config["input"]
val output_file = config["output"]
check(input_file.ends_with(".spl"))
check(output_file.ends_with(".out"))
```

</details>


</details>

<details>
<summary>Advanced: error propagation</summary>

#### error propagation _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error = nil
if error == nil:
    check(true)
else:
    check(false)
```

</details>


</details>

<details>
<summary>Advanced: state transitions</summary>

#### state transitions _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: data pipeline</summary>

#### data pipeline _(slow)_

1. filtered = filtered append
2. transformed = transformed append
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: module interaction</summary>

#### module interaction _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_a = {"export": "value_a"}
val module_b = {"import": module_a["export"]}
check(module_b["import"] == "value_a")
```

</details>


</details>

<details>
<summary>Advanced: nested processing</summary>

#### nested processing _(slow)_

1. flattened = flattened append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: error recovery flow</summary>

#### error recovery flow _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
val result = opt ?? "default"
check(result == "default")
```

</details>


</details>

<details>
<summary>Advanced: full validation</summary>

#### full validation _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
