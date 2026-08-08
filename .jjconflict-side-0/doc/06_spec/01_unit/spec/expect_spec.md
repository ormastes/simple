# expect_spec

> Unit tests for the BDD Expect module.

<!-- sdn-diagram:id=expect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=expect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

expect_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=expect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# expect_spec

Unit tests for the BDD Expect module.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/spec/expect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unit tests for the BDD Expect module.

This test file verifies the expect assertion API used in BDD-style tests:
- Basic expect function with integers, strings, and booleans
- Positive and negative assertions (equality, comparison, negation)
- Chained and complex expectations with nested structures
- Edge cases including zero values, empty strings, and Option types

The expect function is the primary assertion mechanism in the Simple test framework.

## Scenarios

### BDD Expect

#### expect function

#### works with integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 == 42
```

</details>

#### works with strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello" == "hello"
```

</details>

#### works with booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = true
val disabled = false
expect enabled == not disabled
expect disabled == not enabled
```

</details>

#### positive assertions

#### passes when values are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 == 42
```

</details>

#### passes with greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 > 5
```

</details>

#### passes with less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 < 10
```

</details>

#### passes with true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### negative assertions

#### passes when values are not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 != 10
```

</details>

#### passes with negated comparison

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not (5 > 10)
```

</details>

#### passes with false negated

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not false
```

</details>

#### chaining expectations

#### can have multiple expectations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 42
expect value == 42
expect value > 40
expect value < 50
```

</details>

#### can mix positive and negative

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 42
expect value == 42
expect value != 10
expect value > 40
expect not (value > 100)
```

</details>

#### complex assertions

#### handles nested structures

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val age = 30
expect name == "Alice"
expect age > 25
```

</details>

#### handles Option types

1. expect some value is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val some_value = Some(42)
expect some_value.is_some()
```

</details>

#### handles comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val c = 10
expect a == c
expect a != b
expect a < b
expect b > a
```

</details>

#### edge cases

#### handles zero values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 0 == 0
expect 0 < 1
expect 0 > -1
```

</details>

#### handles empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "" == ""
expect "" != "hello"
```

</details>

#### handles None values

1. expect Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Some(42).is_some()
```

</details>

#### type safety

#### works with integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 == 42
expect 42 > 40
```

</details>

#### works with strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello" == "hello"
expect "hello" != "world"
```

</details>

#### works with booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
expect not false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
