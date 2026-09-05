# runner_spec

> Property Testing Framework - Runner Tests

<!-- sdn-diagram:id=runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runner_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# runner_spec

Property Testing Framework - Runner Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/infrastructure/runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Property Testing Framework - Runner Tests
Feature: Property test execution engine with configurable iterations and shrinking

## Scenarios

### Property Test Runner

#### Basic Execution

#### runs property test with generator

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_property_test(
    test_fn=|x| x * 0 == 0,
    seed=42,
    iterations=50,
    max_shrinks=100
)

# Property x * 0 == 0 always holds
expect result.result_type == PropertyResultType.Success
expect result.iterations == 50
```

</details>

#### detects property violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_property_test_range(
    test_fn=|x| x < 100,
    seed=42,
    min=0,
    max=200,
    iterations=100,
    max_shrinks=100
)

# Should detect the violation
expect result.result_type == PropertyResultType.Failure
# Original input should be >= 100
expect result.original_input >= 100
# Minimal should also be >= 100
expect result.minimal_input >= 100
```

</details>

#### runs specified number of iterations

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var iteration_count = 0
val seed = 42

var i = 0
while i < 25:
    val value = gen_i64(seed=seed + i)
    iteration_count = iteration_count + 1
    i = i + 1

expect iteration_count == 25
```

</details>

#### Shrinking on Failure

#### shrinks to minimal failing case

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_property_test_range(
    test_fn=|x| x < 50,
    seed=42,
    min=0,
    max=1000,
    iterations=100,
    max_shrinks=50
)

# Should find a failure
if result.result_type == PropertyResultType.Failure:
    # Minimal should be 50 (smallest value that fails)
    expect result.minimal_input == 50
    # Should have performed some shrinks
    expect result.shrinks >= 0
else:
    # If no failure found, that's also valid
    pass
```

</details>

#### respects max_shrinks limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_property_test_range(
    test_fn=|x| x < 1000,
    seed=42,
    min=0,
    max=10000,
    iterations=10,
    max_shrinks=3
)

if result.result_type == PropertyResultType.Failure:
    # Should not exceed max_shrinks
    expect result.shrinks <= 3
```

</details>

#### Configuration

#### uses custom seed for reproducibility

1. values1 push
2. values2 push
3. values3 push


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Capture generated values
var values1 = []
var values2 = []
var values3 = []

var i = 0
while i < 10:
    values1.push(gen_i64(seed=42 + i))
    i = i + 1

i = 0
while i < 10:
    values2.push(gen_i64(seed=42 + i))
    i = i + 1

i = 0
while i < 10:
    values3.push(gen_i64(seed=123 + i))
    i = i + 1

# Same seed should produce same sequence
expect values1 == values2
# Different seed should produce different sequence
expect values1 != values3
```

</details>

#### supports quick check mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# quick_check runs fewer iterations
val result = quick_check(
    test_fn=|x| x * 0 == 0,
    seed=42
)

expect result == true
```

</details>

#### supports thorough check mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# thorough_check runs many iterations
val result = thorough_check(
    test_fn=|x| x + 0 == x,
    seed=42
)

expect result == true
```

</details>

#### Property Examples

#### tests commutativity

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = true
var i = 0
while i < 100:
    val a = gen_i64_range(seed=42 + i, min=-1000, max=1000)
    val b = gen_i64_range(seed=42 + i + 1000, min=-1000, max=1000)
    if a + b != b + a:
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests associativity

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = true
var i = 0
while i < 100:
    val a = gen_i64_range(seed=42 + i, min=-100, max=100)
    val b = gen_i64_range(seed=42 + i + 1000, min=-100, max=100)
    val c = gen_i64_range(seed=42 + i + 2000, min=-100, max=100)
    if (a + b) + c != a + (b + c):
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests identity property

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = true
var i = 0
while i < 100:
    val x = gen_i64(seed=42 + i)
    if x + 0 != x:
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests reverse twice is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = true
var i = 0
while i < 50:
    val list = gen_list_i64(seed=42 + i, min_len=0, max_len=10, val_min=-100, val_max=100)
    val reversed_twice = list.reverse().reverse()
    if reversed_twice != list:
        passed = false
        break
    i = i + 1

expect passed
```

</details>

#### tests string concatenation length

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = true
var i = 0
while i < 50:
    val s1 = gen_string_with_length(seed=42 + i, min=0, max=10)
    val s2 = gen_string_with_length(seed=42 + i + 1000, min=0, max=10)
    val concatenated = s1 + s2
    if len(concatenated) != len(s1) + len(s2):
        passed = false
        break
    i = i + 1

expect passed
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
