# Assert Statement Specification

> expect(x > 0).to_equal(true)

<!-- sdn-diagram:id=assert_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assert_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assert_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assert_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assert Statement Specification

expect(x > 0).to_equal(true)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASSERT-001 to #ASSERT-012 |
| Category | Language \| Contracts |
| Status | Implemented |
| Source | `test/03_system/feature/usage/assert_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Basic assert
expect(x > 0).to_equal(true)

# Assert with message
expect(x > 0, "x must be positive").to_equal(true)

# Assert in function
fn validate(x: i64) -> i64:
expect(x >= 0, "input must be non-negative").to_equal(true)
x * 2
```

## Scenarios

### Basic Assert Statement

#### basic assert compiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
expect(x > 0).to_equal(true)
expect x == 10
```

</details>

#### assert with message compiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
expect(x > 0, "x must be positive").to_equal(true)
expect x == 10
```

</details>

#### multiple assert conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
expect(x < 100).to_equal(true)
expect(x >= 0, "x must be non-negative").to_equal(true)
expect x == 5
```

</details>

### Assert in Functions

#### assert in function body

1. fn validate and compute
   - Expected: x >= 0, "input must be non-negative" is true
   - Expected: x < 1000 is true
2. expect validate and compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn validate_and_compute(x: i64) -> i64:
    expect(x >= 0, "input must be non-negative").to_equal(true)
    expect(x < 1000).to_equal(true)
    x * 2

expect validate_and_compute(50) == 100
```

</details>

#### multiple asserts in function

1. fn validate
   - Expected: x > 0 is true
   - Expected: y > 0 is true
2. expect validate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn validate(x: i64, y: i64) -> i64:
    expect(x > 0).to_equal(true)
    expect(y > 0).to_equal(true)
    expect(x).to_not_equal(y, "x and y must be different")
    x + y

expect validate(10, 20) == 30
```

</details>

### Assert with Expressions

#### assert with comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
expect(a < b).to_equal(true)
expect(a + b).to_equal(30)
expect(a * 2).to_equal(b)
expect true
```

</details>

#### assert with boolean logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
expect(x > 0 and y > 0).to_equal(true)
expect(x < 100 or y < 100).to_equal(true)
expect(not (x < 0)).to_equal(true)
expect true
```

</details>

### Assert in Control Flow

#### assert in if block

1. fn process
   - Expected: x < 1000, "must be under 1000 in positive branch" is true
   - Expected: x >= -100, "must be at least -100" is true
2. expect process


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn process(x: i64) -> i64:
    if x > 0:
        expect(x < 1000, "must be under 1000 in positive branch").to_equal(true)
        x * 2
    else:
        expect(x >= -100, "must be at least -100").to_equal(true)
        -x

expect process(50) == 100
```

</details>

<details>
<summary>Advanced: assert in loop</summary>

#### assert in loop

1. fn sum with validation
   - Expected: i >= 0, "iteration counter must be non-negative" is true
2. expect sum with validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_with_validation(n: i64) -> i64:
    var total = 0
    var i = 0
    while i < n:
        expect(i >= 0, "iteration counter must be non-negative").to_equal(true)
        total = total + i
        i = i + 1
    total

expect sum_with_validation(5) == 10
```

</details>


</details>

### Assert with Function Contracts

#### assert combined with contracts

1. fn compute
2. out
   - Expected: x < 1000, "x must be reasonable" is true
3. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute(x: i64) -> i64:
    in:
        x >= 0
    out(ret):
        ret >= x
    # Runtime assertions for additional validation
    expect(x < 1000, "x must be reasonable").to_equal(true)
    x + 10

expect compute(50) == 60
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
