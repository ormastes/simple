# Coverage System Integration Tests

> System-level tests for the Simple source coverage feature. These tests verify the complete coverage workflow from instrumentation through data collection and reporting.

<!-- sdn-diagram:id=coverage_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coverage_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coverage_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coverage_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage System Integration Tests

System-level tests for the Simple source coverage feature. These tests verify the complete coverage workflow from instrumentation through data collection and reporting.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #674 |
| Category | System/Infrastructure |
| Status | Implemented |
| Source | `test/03_system/infrastructure/coverage_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System-level tests for the Simple source coverage feature.
These tests verify the complete coverage workflow from
instrumentation through data collection and reporting.

## Test Scenarios

1. Basic coverage collection
2. File I/O for coverage reports
3. Multi-module coverage
4. Coverage with different control flow patterns
5. Coverage report parsing

## Scenarios

### Coverage System Integration

#### Basic Workflow

#### collects coverage during normal execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple program execution
val result = compute_fibonacci(10)
expect(result).to_equal(55)

# Coverage should be tracked
val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("version: 1.0")
expect(sdn).to_contain("summary")
```

</details>

#### tracks decisions in conditionals

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = classify_number(5)
expect(x).to_equal("positive")

val y = classify_number(-3)
expect(y).to_equal("negative")

val z = classify_number(0)
expect(z).to_equal("zero")

# Coverage data available
val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

#### Complex Control Flow

<details>
<summary>Advanced: tracks nested loops and conditions</summary>

#### tracks nested loops and conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = matrix_sum(3, 3)
expect(result).to_be_greater_than(0)

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>


</details>

#### tracks match expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = describe_value(1)
val b = describe_value(2)
val c = describe_value(3)

expect(a).to_equal("number")
expect(b).to_equal("text")
expect(c).to_equal("list")

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

#### tracks early returns

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = find_first_even([1, 3, 5, 6, 7])
expect(a).to_equal(Some(6))

val b = find_first_even([1, 3, 5, 7])
expect(b).to_equal(nil)

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

#### Coverage Data Quality

#### provides consistent data across calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
for i in 0..5:
    if i % 2 == 0:
        x = x + 1

val sdn1 = coverage_sdn_or_empty_summary()
val sdn2 = coverage_sdn_or_empty_summary()

# Should get same data
expect(sdn1).to_equal(sdn2)
```

</details>

#### accumulates data until cleared

1. coverage clear coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First execution
val _ = classify_number(5)
val sdn1 = coverage_sdn_or_empty_summary()

# Second execution (no clear)
val _ = classify_number(-5)
val sdn2 = coverage_sdn_or_empty_summary()

# Data should be valid
expect(sdn1).to_contain("summary")
expect(sdn2).to_contain("summary")

# Clear and verify
coverage.clear_coverage()
val sdn3 = coverage_sdn_or_empty_summary()
expect(sdn3).to_contain("total_decisions: 0")
```

</details>

### Multi-Function Coverage

#### tracks coverage across function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_data([1, 2, 3, 4, 5])
expect(result.sum).to_equal(15)
expect(result.count).to_equal(5)
expect(result.has_negative).to_equal(false)

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

#### tracks recursive function coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = factorial(5)
expect(result).to_equal(120)

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

#### tracks mutually recursive functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val even = is_even(10)
val odd = is_odd(10)

expect(even).to_equal(true)
expect(odd).to_equal(false)

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

### Coverage Stress Tests

#### handles many decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for i in 0..1000:
    if i % 2 == 0:
        total = total + 1
    elif i % 3 == 0:
        total = total + 2
    elif i % 5 == 0:
        total = total + 3
    else:
        total = total + 0

expect(total).to_be_greater_than(0)

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

#### handles deeply nested conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = deeply_nested(true, true, true, true, true)
expect(result).to_equal(5)

val result2 = deeply_nested(true, false, true, false, true)
expect(result2).to_equal(1)

val sdn = coverage_sdn_or_empty_summary()
expect(sdn).to_contain("summary")
```

</details>

#### handles rapid clear-execute-collect cycles

1. coverage clear coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for cycle in 0..100:
    coverage.clear_coverage()
    val _ = classify_number(cycle % 3 - 1)
    val _ = coverage_sdn_or_empty_summary()

val final_sdn = coverage_sdn_or_empty_summary()
expect(final_sdn).to_contain("summary")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
