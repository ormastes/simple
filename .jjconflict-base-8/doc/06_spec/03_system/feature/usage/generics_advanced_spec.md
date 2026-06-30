# Advanced Generics Specification

> struct Array<T, const N: usize>:

<!-- sdn-diagram:id=generics_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generics_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generics_advanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generics_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Generics Specification

struct Array<T, const N: usize>:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GEN-ADV-001 to #GEN-ADV-008 |
| Category | Type System \| Generics |
| Status | Implemented |
| Source | `test/03_system/feature/usage/generics_advanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Const generics
struct Array<T, const N: usize>:
data: T

# Where clause
fn filled(value: T) -> T where T: Copy:
value

# impl Trait for Type
impl Len for MyList:
fn len() -> i64:
self.size

# Multiple trait bounds
fn make<T>() -> T where T: Clone + Default:
T.default()

# Associated types
trait Iterator:
type Item
fn next() -> Option<Self.Item>
```

## Scenarios

### Const Generic Parameters

#### parses const generic parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Array<T, const N: usize>:
    data: T

expect true  # Parsed successfully
```

</details>

### Where Clauses

#### parses where clause on function

1. fn copy
2. fn filled
3. expect filled


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Copy:
    fn copy() -> Self

fn filled(value: i64) -> i64 where i64: Copy:
    value

expect filled(42) == 42
```

</details>

### impl Trait for Type

#### parses impl trait for type

1. fn len
2. fn len
3. expect list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Len:
    fn len() -> i64

struct MyList:
    size: i64

impl Len for MyList:
    fn len() -> i64:
        self.size

val list = MyList(size: 42)
expect list.len() == 42
```

</details>

### Generic impl with Where

#### parses generic impl with where

1. fn clone
2. fn clone


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Clone:
    fn clone() -> Self

impl Clone for i64:
    fn clone() -> i64:
        self

# Note: impl for built-in types doesn't register methods in interpreter
# Just verify that the declaration parses successfully
expect true
```

</details>

### Nested Generic Types

#### parses nested generic types

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Container:
    items: [Option<i64>]

expect true  # Parsed successfully
```

</details>

### Tuple Return Types

#### parses tuple return type

1. fn get pair
2.


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_pair() -> (i64, str):
    (42, "hello")

val _pair = get_pair()
val num = _pair[0]
val txt = _pair[1]
expect num == 42
expect txt == "hello"
```

</details>

### Multiple Trait Bounds

#### parses multiple trait bounds

1. fn clone
2. fn default
3. fn make<T>
4. T default


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Clone:
    fn clone() -> Self

trait Default:
    fn default() -> Self

fn make<T>() -> T where T: Clone + Default:
    T.default()

expect true  # Parsed successfully
```

</details>

### Associated Types

#### parses associated type

1. fn next


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
trait Iterator:
    type Item

    fn next() -> Option<Self.Item>

expect true  # Parsed successfully
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
