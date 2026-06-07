# Let Memoization Specification

> <details>

<!-- sdn-diagram:id=let_memoization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=let_memoization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

let_memoization_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=let_memoization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Let Memoization Specification

## Scenarios

### Let Memoization (TEST-012)

### val (eager - before_each)

#### basic usage

#### provides the value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect x == 10
```

</details>

#### value is available in each example

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect x == 10
```

</details>

### let_lazy (true lazy memoization)

#### basic lazy evaluation

#### can access lazy value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val memo_val = get_let(:lazy_value)
expect memo_val == 42
```

</details>

#### multiple lazy values

#### accesses first value

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:first) == 10
```

</details>

#### accesses second value

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:second) == 20
```

</details>

### has_let helper

#### checking existence

#### returns true for defined let_lazy

1. expect has let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect has_let(:defined_value)
```

</details>

### get_let helper

#### accessing lazy values

#### returns the value

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:accessible) == "hello"
```

</details>

### combining val and let_lazy

#### in same context

#### eager value is accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect eager == 10
```

</details>

#### lazy value is accessible

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:lazy) == 20
```

</details>

#### with given_lazy

#### given_lazy is accessible

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:given_value) == 5
```

</details>

### nested lazy values

#### with dependencies

#### outer is accessible

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:outer) == 10
```

</details>

#### middle is accessible

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:middle) == 20
```

</details>

### Let Memoization Edge Cases

#### lazy value with simple types

#### handles string values

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:string_val) == "test string"
```

</details>

#### handles i32 values

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:int_val) == 42
```

</details>

#### handles bool values

1. expect get let


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect get_let(:bool_val) == true
```

</details>

#### lazy value with list

#### handles list values

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = get_let(:list_val)
expect len(list) == 3
expect list[0] == 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/let_memoization_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Let Memoization (TEST-012)
- val (eager - before_each)
- let_lazy (true lazy memoization)
- has_let helper
- get_let helper
- combining val and let_lazy
- nested lazy values
- Let Memoization Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
