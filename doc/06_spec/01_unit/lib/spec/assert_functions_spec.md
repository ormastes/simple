# Assert Functions Specification

> 1. assert true

<!-- sdn-diagram:id=assert_functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assert_functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assert_functions_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assert_functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assert Functions Specification

## Scenarios

### standalone assert functions

#### assert_true passes for true

1. assert true


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(true)
```

</details>

#### assert_false passes for false

1. assert false


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_false(false)
```

</details>

#### assert_equal passes for equal integers

1. assert equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(42, 42)
```

</details>

#### assert_equal passes for equal strings

1. assert equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal("hello", "hello")
```

</details>

#### assert_not_equal passes for different values

1. assert not equal


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_not_equal(1, 2)
```

</details>

#### assert_contains passes when substring is present

1. assert contains


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_contains("hello world", "world")
```

</details>

#### assert_nil passes for nil

1. assert nil


<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_nil(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/spec/assert_functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- standalone assert functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
