# Pattern Matching Specification

> 1. fn classify

<!-- sdn-diagram:id=pattern_matching_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pattern_matching_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pattern_matching_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pattern_matching_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pattern Matching Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PATTERN-MATCH |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/pattern_matching_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Key Behaviors

- Pattern matching deconstructs values into their components
- Variables bound in patterns are available in match arm bodies
- Patterns include literals, enums, tuples, records, and wildcards

## Scenarios

### Basic Pattern Matching

#### matches exact literal values

1. fn classify
2. expect classify
3. expect classify
4. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x):
    match x:
        0 =>
            return 0
        1 =>
            return 1
        _ =>
            return 99
expect classify(0) == 0
expect classify(1) == 1
expect classify(42) == 99
```

</details>

#### matches with wildcard pattern

1. fn always match
2. expect always match
3. expect always match


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn always_match(x):
    match x:
        _ =>
            return 42
expect always_match(100) == 42
expect always_match(-1) == 42
```

</details>

#### binds value to variable

1. fn double it
2. expect double it
3. expect double it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_it(x):
    match x:
        n =>
            return n * 2
expect double_it(5) == 10
expect double_it(0) == 0
```

</details>

### Tuple Pattern Matching

#### matches tuple and extracts elements

1. fn sum pair
2.
3. expect sum pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_pair(pair):
    match pair:
        (a, b) =>
            return a + b
expect sum_pair((10, 20)) == 30
```

</details>

#### matches nested tuples

1. fn extract first
2.
3. expect extract first


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn extract_first(nested):
    match nested:
        ((a, _), _) =>
            return a
expect extract_first(((5, 10), 20)) == 5
```

</details>

#### matches with partial wildcard

1. fn get first
2.
3. expect get first


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_first(pair):
    match pair:
        (x, _) =>
            return x
expect get_first((42, 100)) == 42
```

</details>

### Enum Pattern Matching

#### matches Option Some variant

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
var result = 0
match opt:
    Some(x) =>
        result = x
    None =>
        result = -1
expect result == 42
```

</details>

#### matches Option None variant

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
var result = 0
match opt:
    Some(x) =>
        result = x
    None =>
        result = -1
expect result == -1
```

</details>

#### matches Result Ok variant

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Ok(100)
var result = 0
match res:
    Ok(x) =>
        result = x
    Err(_) =>
        result = -1
expect result == 100
```

</details>

### Pattern Matching in Functions

#### uses match as expression

1. fn sign
2. expect sign
3. expect sign
4. expect sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sign(x):
    return match x:
        n if n > 0 =>
            1
        n if n < 0 =>
            -1
        _ =>
            0
expect sign(10) == 1
expect sign(-5) == -1
expect sign(0) == 0
```

</details>

#### matches multiple patterns

1. fn is special
2. expect is special
3. expect is special
4. expect is special


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn is_special(x):
    match x:
        0 =>
            return true
        1 =>
            return true
        _ =>
            return false
expect is_special(0) == true
expect is_special(1) == true
expect is_special(5) == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
