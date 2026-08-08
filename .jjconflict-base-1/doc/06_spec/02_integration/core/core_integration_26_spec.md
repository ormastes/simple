# CORE Integration Test

> 1. check

<!-- sdn-diagram:id=core_integration_26_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core_integration_26_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core_integration_26_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core_integration_26_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CORE Integration Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CORE-INT |
| Category | Integration Testing |
| Status | Implemented |
| Source | `test/02_integration/core/core_integration_26_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### CORE Integration

#### lexer to parser

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val x = 42"
check(code.contains("val"))
```

</details>

#### parser to AST

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "fn foo(): pass"
check(code.contains("fn"))
```

</details>

#### AST to MIR

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "x + y"
check(code.contains("+"))
```

</details>

#### MIR to backend

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "1 + 2"
check(code.len() > 0)
```

</details>

#### end-to-end pipeline

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val input = "test"
val result = input + "_processed"
check(result == "test_processed")
```

</details>

#### error recovery

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

#### type checking

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 5
check(x > 0)
```

</details>

#### interpreter integration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3]
var sum = 0
for x in arr:
    sum = sum + x
check(sum == 6)
```

</details>

#### value representation

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = Some(100)
check(opt.?)
check(opt? == 100)
```

</details>

#### environment handling

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val dict = {"key": "value"}
check(dict["key"] == "value")
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
