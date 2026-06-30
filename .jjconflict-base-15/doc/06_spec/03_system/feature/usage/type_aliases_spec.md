# Type Aliases Specification

> Type aliases allow creating alternative names for existing types, improving code readability and maintainability. They enable domain-specific naming without introducing new types, and support generic type aliases for parameterized type shortcuts.

<!-- sdn-diagram:id=type_aliases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_aliases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_aliases_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_aliases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Aliases Specification

Type aliases allow creating alternative names for existing types, improving code readability and maintainability. They enable domain-specific naming without introducing new types, and support generic type aliases for parameterized type shortcuts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TYPE-ALIAS-001 to #TYPE-ALIAS-012 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/type_aliases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Type aliases allow creating alternative names for existing types, improving
code readability and maintainability. They enable domain-specific naming
without introducing new types, and support generic type aliases for
parameterized type shortcuts.

## Syntax

```simple
type UserId = i64
type IntList = [i64]
type StringMap = {str: str}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Alias | Alternative name for an existing type |
| Collection Alias | Alias for array or dict types |
| Alias Chain | Alias that references another alias |

## Behavior

- Type aliases are fully interchangeable with their target type
- Aliases can reference collection types
- Aliases do not create new types (unlike newtypes)
- Aliases can reference other aliases (chaining)

## Scenarios

### Type Aliases

#### with simple aliases

#### aliases primitive types

1. expect user to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type UserId = i64
val user: UserId = 42
expect user to eq(42)
```

</details>

#### allows alias in function signature

1. fn double score
2. expect result to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Score = i64

fn double_score(s: Score) -> Score:
    s * 2

val result = double_score(21)
expect result to eq(42)
```

</details>

#### is interchangeable with base type

1. fn process int
2. expect result to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Age = i64

fn process_int(n: i64) -> i64:
    n + 10

val age: Age = 25
val result = process_int(age)
expect result to eq(35)
```

</details>

#### with collection aliases

#### aliases array types

1. expect numbers len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type IntList = [i64]
val numbers: IntList = [1, 2, 3, 4, 5]
expect numbers.len() to eq(5)
```

</details>

#### aliases dict types

1. expect data["key"] to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type StringMap = {str: str}
val data: StringMap = {"key": "value"}
expect data["key"] to eq("value")
```

</details>

#### allows nested collection aliases

1. expect m[0][0] to eq
2. expect m[1][1] to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Matrix = [[i64]]
val m: Matrix = [[1, 2], [3, 4]]
expect m[0][0] to eq(1)
expect m[1][1] to eq(4)
```

</details>

#### with alias chains

#### supports alias of alias

1. expect user to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Id = i64
type UserId = Id
val user: UserId = 100
expect user to eq(100)
```

</details>

#### supports multiple levels of aliasing

1. expect value to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Base = i64
type Middle = Base
type Top = Middle
val value: Top = 42
expect value to eq(42)
```

</details>

### Type Alias Usage

#### in struct fields

#### uses alias in struct definition

1. expect e time to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Timestamp = i64

class Event:
    time: Timestamp
    name: str

val e = Event(time: 1234567890, name: "test")
expect e.time to eq(1234567890)
```

</details>

#### in class fields

#### uses alias in class definition

1. fn get
2. expect c get


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Count = i64

class Counter:
    value: Count

    fn get() -> Count:
        self.value

val c = Counter(value: 10)
expect c.get() to eq(10)
```

</details>

#### with return types

#### uses alias as return type

1. fn compute
2. expect r to eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Result = i64

fn compute() -> Result:
    42

val r: Result = compute()
expect r to eq(42)
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
