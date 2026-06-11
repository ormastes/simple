# Type System Unit Tests

> 1. check

<!-- sdn-diagram:id=type_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type System Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-TYPES-002 |
| Category | Compiler \| Types |
| Status | Implemented |
| Source | `test/01_unit/compiler/types/type_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Primitive Types

#### i64 type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
check(x == 42)
```

</details>

#### f64 type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: f64 = 3.14
check(x > 3.0)
```

</details>

#### bool type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: bool = true
check(x)
```

</details>

#### text type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: text = "hello"
check(x == "hello")
```

</details>

#### unit type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ()
check(true)
```

</details>

### Composite Types

#### array type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### optional type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: Option<i64> = Some(42)
check(x.?)
```

</details>

#### tuple type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = (1, "hello")
check(true)
```

</details>

#### map type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = {"key": "value"}
check(m.len() == 1)
```

</details>

### Type Conversions

#### i64 to f64

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
val y = x.to_f64()
check(y > 41.0 and y < 43.0)
```

</details>

#### f64 to i64

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: f64 = 42.7
val y = x.to_i64()
check(y == 42)
```

</details>

#### i64 to text

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
val s = "{x}"
check(s == "42")
```

</details>

#### bool to text

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
val s = "{x}"
check(s == "true")
```

</details>

### Type Aliases

#### type alias basic

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
type Number = i64
val x: Number = 42
check(x == 42)
```

</details>

### Type Checking Errors

#### type mismatch is error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "type_mismatch"
check(error == "type_mismatch")
```

</details>

#### undeclared type is error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "undeclared_type"
check(error == "undeclared_type")
```

</details>

#### incompatible return type is error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "incompatible_return"
check(error == "incompatible_return")
```

</details>

#### argument count mismatch is error

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "arg_count_mismatch"
check(error == "arg_count_mismatch")
```

</details>

### Subtyping

#### nil is subtype of Option

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: Option<i64> = nil
check(x.?() == false)
```

</details>

#### Some is subtype of Option

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: Option<i64> = Some(42)
check(x.?)
```

</details>

### Type Constraints

#### numeric constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val y = x + 1
check(y == 43)
```

</details>

#### equality constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val y = 42
check(x == y)
```

</details>

#### ordering constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val y = 5
check(x < y)
```

</details>

#### string constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = "hello"
check(x.len() == 5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
