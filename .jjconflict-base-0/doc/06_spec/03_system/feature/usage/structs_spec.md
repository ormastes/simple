# Structs Specification

> Structs are user-defined data types that group related fields together. They support named fields with type annotations, default values, and can have methods defined via impl blocks. Structs are the primary way to define custom data structures in Simple.

<!-- sdn-diagram:id=structs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=structs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

structs_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=structs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Structs Specification

Structs are user-defined data types that group related fields together. They support named fields with type annotations, default values, and can have methods defined via impl blocks. Structs are the primary way to define custom data structures in Simple.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/structs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Structs are user-defined data types that group related fields together.
They support named fields with type annotations, default values, and can
have methods defined via impl blocks. Structs are the primary way to
define custom data structures in Simple.

## Syntax

```simple
struct Point:
x: i64
y: i64

struct Config:
host: String = "localhost"
port: i64 = 8080

val p = Point { x: 3, y: 4 }
val c = Config { port: 9000 }  # host uses default
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Struct | User-defined data type with named fields |
| Field | Named member of a struct with type annotation |
| Default Value | Optional value used when field not provided |
| Construction | Creating struct instance with field values |

## Behavior

- Fields are accessed using dot notation: `point.x`
- Construction requires all fields without defaults
- Fields can have default values
- Structs are value types (copied by default)

## Scenarios

### Structs

#### struct definition and construction

#### defines struct with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

val p = Point { x: 10, y: 20 }
expect p.x + p.y == 30
```

</details>

#### constructs struct with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Config:
    host: str
    port: i64

val c = Config { host: "localhost", port: 8080 }
expect c.port == 8080
```

</details>

#### struct field access

#### accesses struct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Rectangle:
    width: i64
    height: i64

val r = Rectangle { width: 10, height: 5 }
expect r.width * r.height == 50
```

</details>

### Impl Blocks

#### adds method to struct

1. fn sum
2. expect p sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

impl Point:
    fn sum(self):
        return self.x + self.y

val p = Point { x: 15, y: 25 }
expect p.sum() == 40
```

</details>

#### adds method with arguments

1. fn add
2. expect c add


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Counter:
    value: i64

impl Counter:
    fn add(self, n):
        return self.value + n

val c = Counter { value: 10 }
expect c.add(5) == 15
```

</details>

### Classes

#### defines class with static method

1. static fn add
2. expect Calculator add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Calculator:
    static fn add(a, b):
        return a + b

expect Calculator.add(3, 4) == 7
```

</details>

### Context Blocks

#### dispatches methods to context object

1. fn double
2. res = double


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Calculator:
    fn double(self, x):
        return x * 2

val calc = Calculator {}
var res = 0
context calc:
    res = double(21)
expect res == 42
```

</details>

#### accesses self fields in context

1. fn add
2. res = add


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Adder:
    base: i64 = 10

    fn add(self, x):
        return self.base + x

val a = Adder { base: 30 }
var res = 0
context a:
    res = add(12)
expect res == 42
```

</details>

### Method Missing

#### calls method_missing for unknown method

1. fn method missing
2. expect d unknown method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class DSL:
    fn method_missing(self, name, args, block):
        return 42

val d = DSL {}
expect d.unknown_method() == 42
```

</details>

#### passes arguments to method_missing

1. fn method missing
2. expect m any method


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Multiplier:
    factor: i64 = 10

    fn method_missing(self, name, args, block):
        val x = args[0]
        return self.factor * x

val m = Multiplier { factor: 7 }
expect m.any_method(6) == 42
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
