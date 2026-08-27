# shrinking_spec

> Property Testing Framework - Shrinking Tests

<!-- sdn-diagram:id=shrinking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shrinking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shrinking_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shrinking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shrinking_spec

Property Testing Framework - Shrinking Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/shrinking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Property Testing Framework - Shrinking Tests
Feature: Automatic input minimization to find minimal failing test cases

## Scenarios

### Shrinking Algorithm

#### Integer Shrinking

#### shrinks positive integers towards zero

1. expect candidates contains
2. expect candidates contains
3. expect candidates contains
4. expect c abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_i64(100)
# Should include 0
expect candidates.contains(0)
# Should include value/2 = 50
expect candidates.contains(50)
# Should include value-1 = 99
expect candidates.contains(99)
# All candidates should be smaller in absolute value
for c in candidates:
    expect c.abs() <= 100
```

</details>

#### shrinks negative integers towards zero

1. expect candidates contains
2. expect candidates contains
3. expect candidates contains
4. expect c abs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_i64(-100)
# Should include 0
expect candidates.contains(0)
# Should include value/2 = -50
expect candidates.contains(-50)
# Should include value+1 = -99
expect candidates.contains(-99)
# All candidates should be closer to zero
for c in candidates:
    expect c.abs() <= 100
```

</details>

#### cannot shrink zero

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_i64(0)
# Zero cannot be shrunk further
expect len(candidates) == 0
```

</details>

#### List Shrinking

#### shrinks to empty list

1. expect candidates contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_list([1, 2, 3, 4, 5])
# Should include empty list as candidate
expect candidates.contains([])
```

</details>

#### shrinks by removing half

1. expect candidates contains
2. expect candidates contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_list([1, 2, 3, 4, 5, 6])
# Should include first half [1, 2, 3]
expect candidates.contains([1, 2, 3])
# Should include second half [4, 5, 6]
expect candidates.contains([4, 5, 6])
```

</details>

#### shrinks by removing first element

1. expect candidates contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_list([1, 2, 3])
# Should include list with first element removed
expect candidates.contains([2, 3])
```

</details>

#### shrinks by removing last element

1. expect candidates contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_list([1, 2, 3])
# Should include list with last element removed
expect candidates.contains([1, 2])
```

</details>

#### cannot shrink empty list

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_list([])
# Empty list cannot be shrunk
expect len(candidates) == 0
```

</details>

#### text Shrinking

#### shrinks to empty string

1. expect candidates contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_string("hello")
# Should include empty string
expect candidates.contains("")
```

</details>

#### shrinks by removing characters

1. expect len
2. expect candidates contains
3. expect candidates contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_string("hello")
# Should have multiple candidates
expect len(candidates) > 1
# Should include substring from start
expect candidates.contains("he")
# Should include substring with first char removed
expect candidates.contains("ello")
```

</details>

#### cannot shrink empty string

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_string("")
# Empty string cannot be shrunk
expect len(candidates) == 0
```

</details>

#### Full Shrinking Process

#### finds minimal failing case for integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property: value must be < 50
val test_fn = |x| x < 50

# Start with failing value 100
val result = shrink_to_minimal(
    failing_value: 100,
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Should shrink to minimal failing value (50)
expect result.result_type == ShrinkResultType.MinimalFailure
expect result.value == 50
expect result.shrinks > 0
```

</details>

#### finds minimal failing case for lists

1. expect list sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property: list sum must be < 10
val test_fn = |list| list_sum(list) < 10

# Start with failing list that sums to > 10
val (result_type, value, shrinks) = shrink_list_to_minimal(
    failing_list: [3, 3, 3, 3, 3],
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Should shrink to a minimal failing list
expect result_type == ShrinkResultType.MinimalFailure
expect list_sum(value) >= 10
```

</details>

#### handles max_shrinks limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property that always fails
val test_fn = |x| false

val result = shrink_to_minimal(
    failing_value: 1000000,
    test_fn: test_fn,
    max_shrinks: 5,
    max_depth: 10
)

# Should hit max_shrinks limit or find minimal
expect result.shrinks <= 5
```

</details>

#### handles max_depth limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property that always fails
val test_fn = |x| false

val result = shrink_to_minimal(
    failing_value: 100,
    test_fn: test_fn,
    max_shrinks: 1000,
    max_depth: 3
)

# Should terminate due to depth limit
expect result.result_type == ShrinkResultType.MinimalFailure or result.result_type == ShrinkResultType.MaxShrinksExceeded
```

</details>

#### Edge Cases

#### handles no shrink possible

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Zero cannot be shrunk
val test_fn = |x| x > 0

val result = shrink_to_minimal(
    failing_value: 0,
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Should report minimal with 0 value
expect result.value == 0
expect result.shrinks == 0
```

</details>

#### handles all shrinks passing

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Property: value must be exactly 42
val test_fn = |x| x == 42

# Start with failing value 100 (which is != 42)
val result = shrink_to_minimal(
    failing_value: 100,
    test_fn: test_fn,
    max_shrinks: 100,
    max_depth: 10
)

# Shrink candidates (0, 50, 99) all fail since they're not 42
# Eventually we'll find 0 as the minimal value != 42
expect result.value != 42
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
