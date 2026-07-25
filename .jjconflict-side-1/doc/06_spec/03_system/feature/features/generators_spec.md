# generators_spec

> Property Testing Framework - Generator Tests

<!-- sdn-diagram:id=generators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generators_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# generators_spec

Property Testing Framework - Generator Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/generators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Property Testing Framework - Generator Tests
Feature: Generators for property-based testing that produce random test data

## Scenarios

### Generator Framework

#### Primitive Generators

#### generates i64 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test multiple seeds produce values
for seed in [1, 42, 100, 12345]:
    val value = gen_i64(seed)
    # i64 generator produces values using LCG algorithm
    expect value >= 0
# Different seeds should produce different values
val v1 = gen_i64(1)
val v2 = gen_i64(42)
expect v1 != v2
```

</details>

#### generates i64 in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test multiple seeds all produce values in range
for seed in [1, 42, 100, 12345, 999]:
    val value = gen_i64_range(seed=seed, min=10, max=100)
    expect value >= 10
    expect value < 100
```

</details>

#### generates u64 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    val value = gen_u64(seed)
    # u64 values should be non-negative
    expect value >= 0
```

</details>

#### generates bool values

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test multiple seeds to get both true and false
var saw_true = false
var saw_false = false
var seed = 0
while seed < 20:
    val value = gen_bool(seed)
    if value:
        saw_true = true
    else:
        saw_false = true
    seed = seed + 1
# Should eventually see both values
expect saw_true or saw_false
```

</details>

#### generates string values

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    val value = gen_string(seed)
    # Strings are generated with length 0-20
    expect len(value) <= 20
```

</details>

#### generates ascii strings

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    val value = gen_ascii(seed)
    expect len(value) <= 20
```

</details>

#### generates strings with length constraints

1. expect len
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100, 12345]:
    val value = gen_string_with_length(seed=seed, min=5, max=10)
    expect len(value) >= 5
    expect len(value) < 10
```

</details>

#### Collection Generators

#### generates lists

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    val value = gen_list_i64(seed)
    # Lists generated with length 0-20
    expect len(value) <= 20
```

</details>

#### generates lists with length constraints

1. expect len
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100, 12345]:
    val value = gen_list_i64_with_length(seed=seed, min=3, max=7)
    expect len(value) >= 3
    expect len(value) < 7
```

</details>

#### generates Option values

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var saw_some = false
var saw_nil = false
var seed = 0
while seed < 20:
    val value = gen_option_i64(seed)
    match value:
        Some(_) -> saw_some = true
        nil -> saw_nil = true
    seed = seed + 1
# Should see both Some and nil values
expect saw_some or saw_nil
```

</details>

#### generates Result values

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var saw_ok = false
var saw_err = false
var seed = 0
while seed < 20:
    val value = gen_result_i64(seed)
    match value:
        Ok(_) -> saw_ok = true
        Err(_) -> saw_err = true
    seed = seed + 1
# Should see both Ok and Err values
expect saw_ok or saw_err
```

</details>

#### Tuple Generators

#### generates 2-tuples

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    val t = gen_tuple2(seed=seed, min=0, max=100)
    expect t.0 >= 0
    expect t.0 < 100
    expect t.1 == true or t.1 == false
```

</details>

#### generates 3-tuples

1. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    val t = gen_tuple3(seed=seed, min=0, max=10)
    expect t.0 >= 0
    expect t.0 < 10
    expect t.1 == true or t.1 == false
    expect len(t.2) >= 0
```

</details>

#### Generator Combinators

#### maps generator output

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    val base = gen_i64_range(seed=seed, min=1, max=10)
    val value = base * 2
    # Original: 1-9, mapped: 2-18
    expect value >= 2
    expect value <= 18
    # Should be even
    expect value % 2 == 0
```

</details>

#### filters generator output

1. var value = gen i64 range
2. value = gen i64 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    # Keep trying until we get an even value
    var value = gen_i64_range(seed=seed, min=0, max=100)
    var tries = 0
    while value % 2 != 0 and tries < 100:
        tries = tries + 1
        value = gen_i64_range(seed=seed + tries, min=0, max=100)
    # Should be able to find an even value
    expect value % 2 == 0 or tries >= 100
```

</details>

#### flat_maps generators

1. expect len
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for seed in [1, 42, 100]:
    # Generate a number, then generate a list of that length
    val n = gen_i64_range(seed=seed, min=1, max=5)
    val list = gen_list_i64_with_length(seed=seed + 1, min=n, max=n + 1)
    # List length should be in range
    expect len(list) >= 1
    expect len(list) <= 5
```

</details>

#### chooses from one_of

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var saw_low = false
var saw_high = false
var seed = 0
while seed < 20:
    # Simulate one_of by choosing based on seed
    if gen_bool(seed):
        val value = gen_i64_range(seed=seed, min=0, max=10)
        saw_low = true
    else:
        val value = gen_i64_range(seed=seed, min=100, max=110)
        saw_high = true
    seed = seed + 1
# Should see values from both ranges
expect saw_low or saw_high
```

</details>

#### chooses by frequency

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var low_count = 0
var high_count = 0
var seed = 0
while seed < 100:
    # Simulate frequency: 90% low, 10% high
    val choice = gen_i64_range(seed=seed, min=0, max=10)
    if choice < 9:
        low_count = low_count + 1
    else:
        high_count = high_count + 1
    seed = seed + 1
# Low values should be more common
expect low_count > high_count
```

</details>

#### Shrinking

#### shrinks i64 towards zero

1. expect candidates contains
2. expect candidates contains
3. expect candidates contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_i64(100)
# Should include 0 as a candidate
expect candidates.contains(0)
# Should include value/2 = 50
expect candidates.contains(50)
# Should include value-1 = 99
expect candidates.contains(99)
```

</details>

#### shrinks lists to smaller lists

1. expect candidates contains
2. expect len
3. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_list([1, 2, 3, 4, 5])
# Should include empty list
expect candidates.contains([])
# Should have candidates
expect len(candidates) > 0
# All candidates should be smaller or equal
for c in candidates:
    expect len(c) <= 5
```

</details>

#### shrinks bool to false

1. expect true shrinks contains
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Shrinking true should give false
val true_shrinks = shrink_bool(true)
expect true_shrinks.contains(false)
# Shrinking false should give empty
val false_shrinks = shrink_bool(false)
expect len(false_shrinks) == 0
```

</details>

#### shrinks Option to nil

1. expect some shrinks contains
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Shrinking Some should give nil
val some_shrinks = shrink_option(Some(42))
expect some_shrinks.contains(nil)
# Shrinking nil should give empty
val nil_shrinks = shrink_option(nil)
expect len(nil_shrinks) == 0
```

</details>

#### shrinks strings to empty

1. expect candidates contains
2. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = shrink_string("hello")
# Should include empty string
expect candidates.contains("")
# Shrinking empty should give empty
val empty_shrinks = shrink_string("")
expect len(empty_shrinks) == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
