# Advanced Pattern Matching Specification

> match x:

<!-- sdn-diagram:id=pattern_matching_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_matching_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_matching_advanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_matching_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Pattern Matching Specification

match x:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PAT-ADV-001 to #PAT-ADV-018 |
| Category | Language \| Pattern Matching |
| Status | Implemented |
| Source | `test/03_system/feature/usage/pattern_matching_advanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Match guards
match x:
n if n > 0 => "positive"
n if n < 0 => "negative"
_ => "zero"

# If val (if let is deprecated)
if val Some(value) = opt:
print(value)

# While val (while let is deprecated)
while val Some(item) = iterator.next():
process(item)

# Or patterns
match x:
1 | 2 | 3 => "small"
_ => "large"

# Range patterns
match x:
0..10 => "single digit"
10..100 => "double digit"
_ => "large"
```

## Scenarios

### Match Guards

#### matches with basic guard

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> i64:
    match x:
        n if n < 0 =>
            -1
        n if n == 0 =>
            0
        n if n > 0 =>
            1
    -99

expect classify(5) == 1
```

</details>

#### matches negative with guard

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> i64:
    match x:
        n if n < 0 =>
            -1
        n if n == 0 =>
            0
        n if n > 0 =>
            1
    -99

expect classify(-10) == -1
```

</details>

#### uses binding in guard

1. fn verify
2.
3.
4. expect verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn verify(pair: (i64, i64)) -> i64:
    match pair:
        (a, b) if a + b > 10 =>
            1
        (a, b) if a + b == 10 =>
            0
        _ =>
            -1

expect verify((7, 5)) == 1  # 7 + 5 = 12 > 10
```

</details>

#### falls through when guard fails

1. fn test
2. expect test


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64) -> i64:
    match x:
        n if n > 100 =>
            100
        n if n > 10 =>
            10
        n =>
            n

expect test(50) == 10  # 50 > 100? No. 50 > 10? Yes
```

</details>

### If Val Expressions

#### matches Some with if val

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
var res = 0
if val Some(x) = opt:
    res = x
expect res == 42
```

</details>

#### uses else branch for non-matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = nil
var res = 0
if val Some(x) = opt:
    res = x
else:
    res = -1
expect res == -1
```

</details>

#### matches Ok with if val

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Ok(100)
var output = 0
if val Ok(value) = res:
    output = value
expect output == 100
```

</details>

#### matches Some with if var

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
var res = 0
if var Some(x) = opt:
    res = x
expect res == 42
```

</details>

### While Let Expressions

<details>
<summary>Advanced: loops while pattern matches</summary>

#### loops while pattern matches

1. fn next item
2. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn next_item(n: i64) -> Option<i64>:
    if n > 0:
        Some(n)
    else:
        None

var counter = 3
var sum = 0
while let Some(value) = next_item(counter):
    sum = sum + value
    counter = counter - 1
expect sum == 6  # 3 + 2 + 1
```

</details>


</details>

### Or Patterns

#### matches multiple literals

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> i64:
    match x:
        1 | 2 | 3 =>
            1  # small
        4 | 5 | 6 =>
            2  # medium
        _ =>
            3  # large

expect classify(2) == 1
```

</details>

#### matches medium group

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> i64:
    match x:
        1 | 2 | 3 =>
            1
        4 | 5 | 6 =>
            2
        _ =>
            3

expect classify(5) == 2
```

</details>

#### falls through to wildcard

1. fn verify
2. expect verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn verify(x: i64) -> i64:
    match x:
        0 | 1 =>
            10
        _ =>
            99

expect verify(99) == 99
```

</details>

### Range Patterns

#### matches exclusive range

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> i64:
    match x:
        0..10 =>
            1
        10..20 =>
            2
        _ =>
            3

expect classify(5) == 1
```

</details>

#### exclusive range excludes end

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> i64:
    match x:
        0..10 =>
            1
        10..20 =>
            2
        _ =>
            3

expect classify(10) == 2  # 10 not in 0..10
```

</details>

#### matches inclusive range

1. fn classify
2. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> i64:
    match x:
        0..=5 =>
            1
        6..=10 =>
            2
        _ =>
            3

expect classify(5) == 1  # 5 is in 0..=5
```

</details>

### Numeric Literals

#### parses hex literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0xFF
expect x == 255
```

</details>

#### hex arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0x10 + 0x20
expect x == 48  # 16 + 32
```

</details>

#### parses binary literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1010
expect x == 10
```

</details>

#### binary with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0b1111_0000
expect x == 240
```

</details>

#### parses octal literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0o755
expect x == 493  # 7*64 + 5*8 + 5
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
