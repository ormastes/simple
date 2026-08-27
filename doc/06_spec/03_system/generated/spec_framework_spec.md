# spec_framework_spec

> BDD Spec Framework Tests

<!-- sdn-diagram:id=spec_framework_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spec_framework_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spec_framework_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spec_framework_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_framework_spec

BDD Spec Framework Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/spec_framework_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

BDD Spec Framework Tests
Feature: SPipe BDD Testing Framework
Category: Testing, Framework
Status: Complete

Comprehensive tests for the BDD spec framework itself including
describe, context, it, expect, and matcher DSL.

## Scenarios

### BDD Spec Framework

#### describe blocks

#### groups tests by description

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### supports nested context blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### executes blocks in order

1. results push
2. expect len
3. results push
4. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = []
results.push(1)
expect len(results) == 1
results.push(2)
expect len(results) == 2
```

</details>

#### context blocks (nested describes)

#### creates nested example groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### inherits parent context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_val = 42
expect parent_val == 42
```

</details>

#### supports multiple levels of nesting

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level1 = "one"
val level2 = "two"
expect level1 == "one"
expect level2 == "two"
```

</details>

#### it blocks (test definitions)

#### defines a single test case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### supports multiple assertions per test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
expect 2 * 3 == 6
expect "hello" == "hello"
```

</details>

#### can use local variables in tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
val z = x + y
expect z == 30
```

</details>

#### expect assertions

#### asserts equality with ==

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 42 == 42
```

</details>

#### asserts inequality with !=

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 != 6
```

</details>

#### supports boolean assertions

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
expect (not false)
```

</details>

#### supports string comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello" == "hello"
expect "hello" != "world"
```

</details>

#### expect with matchers

#### uses 'to be' for equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 to be 5
```

</details>

#### uses 'to eq' for equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 to eq 5
```

</details>

#### uses 'to be_gt' for greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 to be_gt 5
```

</details>

#### uses 'to be_lt' for less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 to be_lt 10
```

</details>

#### uses 'to include' for string containment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello world" to include "world"
```

</details>

#### uses 'to start_with' for string prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello world" to start_with "hello"
```

</details>

#### uses 'to end_with' for string suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello world" to end_with "world"
```

</details>

#### negated assertions

#### supports 'not_to' for negative assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 not_to eq 6
```

</details>

#### supports multiple negative matchers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 not_to be_lt 5
expect "hello" not_to include "xyz"
```

</details>

#### complex assertions

#### handles complex expressions

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
expect len(a) == 3
```

</details>

#### chains multiple assertions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val computed = 2 + 2
expect computed == 4
expect computed to be_gt 0
expect computed to be_lt 10
```

</details>

#### works with computed values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = a * 2
expect b == 10
val c = 3 * 2
expect c == 6
```

</details>

#### works with conditional logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
if x > 5:
    expect x to be_gt 5
else:
    fail "x should be greater than 5"
```

</details>

#### assertion failures

#### fails with appropriate message on false assertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### can test multiple conditions

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1, 2, 3, 4, 5]
expect len(values) == 5
expect values[0] == 1
expect values[4] == 5
```

</details>

#### describe/context/it structure

#### preserves nested structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### deeply nested

#### supports many levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

#### even deeper

#### continues to work

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
