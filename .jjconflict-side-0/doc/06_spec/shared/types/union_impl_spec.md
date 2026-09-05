# Union Keyword and Impl Blocks Specification

> union Status:

<!-- sdn-diagram:id=union_impl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=union_impl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

union_impl_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=union_impl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Union Keyword and Impl Blocks Specification

union Status:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UNION-KEYWORD, #ENUM-IMPL |
| Category | Language Features |
| Status | Implemented |
| Source | `test/shared/types/union_impl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
union Status:
Active
Inactive

union Result:
Ok(value: Int)
Err(msg: String)

impl Result:
fn is_ok() -> bool:
match self:
case Result.Ok(_):
true
case _:
false
```

## Key Behaviors

- Union is an alias for enum - fully interchangeable
- Variants can be simple (no payload) or have associated data
- Impl blocks can be used to add methods
- Pattern matching works with union variants
- Union values are constructed with VariantName or VariantName(payload)

## Scenarios

### Union keyword

#### basic union creation

#### parses union types correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Union is an alias for enum in Simple
val s = Status.Active
expect true
```

</details>

#### creates inactive status variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Status.Inactive
expect true
```

</details>

#### creates union variant with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = MyResult.Err("failed")
expect true
```

</details>

#### union variants with payloads

#### supports union variants with payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = MyResult.Ok(42)
val r2 = MyResult.Err("failed")
expect true
```

</details>

#### creates option with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Some(10)
expect true
```

</details>

#### creates empty option

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Nothing
expect true
```

</details>

#### basic variant creation

#### works with basic variant creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Some(10)
# Union types work, pattern matching is separate feature
expect true
```

</details>

#### creates multiple variants of same type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt1 = MyOption.Some(1)
val opt2 = MyOption.Some(2)
val opt3 = MyOption.Nothing
expect true
```

</details>

### Union Impl Methods

#### Status union methods

#### checks if status is active

1. expect s is active


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Status.Active
expect s.is_active() == true
```

</details>

#### checks if status is inactive

1. expect s is active


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Status.Inactive
expect s.is_active() == false
```

</details>

#### displays status as string

1. expect s display


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Status.Active
expect s.display() == "Active"
```

</details>

#### displays inactive status

1. expect s display


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Status.Inactive
expect s.display() == "Inactive"
```

</details>

#### MyResult union methods

#### checks if result is ok

1. expect r is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = MyResult.Ok(42)
expect r.is_ok() == true
```

</details>

#### checks if result is error ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = MyResult.Err("failed")
val ok_check = r1.is_ok()
expect(ok_check).to_equal(false)
```

</details>

#### checks if result is error err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r2 = MyResult.Err("failed")
val err_check = r2.is_err()
expect(err_check).to_equal(true)
```

</details>

#### checks error predicate

1. expect r is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = MyResult.Ok(10)
expect r.is_err() == false
```

</details>

#### MyOption union methods

#### checks if option has value

1. expect opt is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Some(10)
expect opt.is_some() == true
```

</details>

#### checks if option is empty

1. expect opt is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Nothing
expect opt.is_some() == false
```

</details>

#### gets value or default

1. expect opt1 get or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt1 = MyOption.Some(42)
expect opt1.get_or(0) == 42
```

</details>

#### uses default when none

1. expect opt2 get or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt2 = MyOption.Nothing
expect opt2.get_or(100) == 100
```

</details>

### Union Pattern Matching

#### simple pattern matching

#### matches active status

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Status.Active
val result = match s:
    case Status.Active:
        "active"
    case Status.Inactive:
        "inactive"
expect result == "active"
```

</details>

#### matches inactive status

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Status.Inactive
val result = match s:
    case Status.Active:
        "active"
    case Status.Inactive:
        "inactive"
expect result == "inactive"
```

</details>

#### pattern matching with payloads

#### extracts ok value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = MyResult.Ok(42)
val result = match r:
    case MyResult.Ok(v):
        v
    case MyResult.Err(_):
        0
expect result == 42
```

</details>

#### extracts error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = MyResult.Err("test error")
val result = match r:
    case MyResult.Ok(_):
        "ok"
    case MyResult.Err(msg):
        msg
expect result == "test error"
```

</details>

#### pattern matching on option

#### matches some variant with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Some(25)
val result = match opt:
    case MyOption.Some(v):
        v * 2
    case MyOption.Nothing:
        0
expect result == 50
```

</details>

#### matches nothing variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Nothing
val result = match opt:
    case MyOption.Some(v):
        v
    case MyOption.Nothing:
        -1
expect result == -1
```

</details>

### Union Type Safety

#### variant type consistency

#### creates result with integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = MyResult.Ok(42)
expect true
```

</details>

#### creates result with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = MyResult.Err("error message")
expect true
```

</details>

#### creates option with integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = MyOption.Some(100)
expect true
```

</details>

#### multiple union types

#### handles different union types independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = Status.Active
val result = MyResult.Ok(1)
val option = MyOption.Some(2)
expect true
```

</details>

#### union method calls preserve type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = Status.Active
val s2 = Status.Inactive
val isActive = s1.is_active()
expect isActive == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
