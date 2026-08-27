# Safe Unwrap Operators Specification

> opt unwrap or: default_value              # Use default if None

<!-- sdn-diagram:id=safe_unwrap_operators_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=safe_unwrap_operators_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

safe_unwrap_operators_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=safe_unwrap_operators_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safe Unwrap Operators Specification

opt unwrap or: default_value              # Use default if None

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OPERATORS-SAFE-UNWRAP |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/safe_unwrap_operators_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
opt unwrap or: default_value              # Use default if None
opt unwrap else: \: lazy_default_expr     # Lazy evaluation of default
result unwrap or_return: default_on_err   # Early return with default
```

## Key Behaviors

- `unwrap or:` evaluates the default value immediately (eager)
- `unwrap else:` takes a closure for lazy evaluation (only called if needed)
- `unwrap or_return:` returns from the function with a default value on error
- Works with both Option<T> and Result<T, E> types
- Provides inline alternatives to verbose pattern matching
- Type-safe: never causes runtime panics

## Scenarios

### Safe Unwrap Operators

#### unwrap or: with eager evaluation

#### returns value when Option is Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
val result = opt unwrap or: 0
expect result == 42
```

</details>

#### returns default when Option is None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
val result = opt unwrap or: 0
expect result == 0
```

</details>

#### works with Result Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res: Result<i64, text> = Ok(42)
val result = res unwrap or: 0
expect result == 42
```

</details>

#### returns default for Result Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res: Result<i64, text> = Err("error")
val result = res unwrap or: -1
expect result == -1
```

</details>

#### evaluates default expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
val result = opt unwrap or: 10 + 5
expect result == 15
```

</details>

#### handles complex default expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<text> = None
val result = opt unwrap or: "default".upper()
expect result == "DEFAULT"
```

</details>

#### works with string defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<text> = None
val result = opt unwrap or: "fallback"
expect result == "fallback"
```

</details>

#### preserves value type through unwrap

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(100)
val result = opt unwrap or: 0
# Type is still i64
expect result == 100
```

</details>

#### unwrap else: with lazy evaluation

#### returns value when Option is Some without calling closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
var called = false
val result = opt unwrap else: \:
    called = true
    99
expect result == 42
expect called == false
```

</details>

#### calls closure only when Option is None

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
var called = false
val result = opt unwrap else: \:
    called = true
    99
expect result == 99
expect called == true
```

</details>

#### works with Result Ok without evaluating closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res: Result<i64, text> = Ok(42)
var called = false
val result = res unwrap else: \:
    called = true
    -1
expect result == 42
expect called == false
```

</details>

#### evaluates closure for Result Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res: Result<i64, text> = Err("failed")
var called = false
val result = res unwrap else: \:
    called = true
    -1
expect result == -1
expect called == true
```

</details>

#### closure can perform side effects

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var side_effect = 0
val opt: Option<i64> = None
val result = opt unwrap else: \:
    side_effect = 100
    42
expect result == 42
expect side_effect == 100
```

</details>

#### lazy evaluation skips expensive computation when value exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(1)
var expensive_called = false
val result = opt unwrap else: \:
    expensive_called = true
    999
expect result == 1
expect expensive_called == false
```

</details>

#### unwrap or_return: with early return

#### returns value when present

1. fn get value or early
2. expect get value or early


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value_or_early() -> i64:
    val opt: Option<i64> = Some(42)
    val value = opt unwrap or_return: 0
    value + 1
expect get_value_or_early() == 43
```

</details>

#### returns default when None

1. fn get value or early
2. expect get value or early


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value_or_early() -> i64:
    val opt: Option<i64> = None
    val value = opt unwrap or_return: 0
    value + 1  # This code never executes
expect get_value_or_early() == 0
```

</details>

#### works with Result

1. fn parse number or early
2. expect parse number or early


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn parse_number_or_early() -> i64:
    val res: Result<i64, text> = Ok(42)
    val value = res unwrap or_return: -1
    value * 2
expect parse_number_or_early() == 84
```

</details>

#### returns default for Result Err

1. fn parse number or early
2. expect parse number or early


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn parse_number_or_early() -> i64:
    val res: Result<i64, text> = Err("parse error")
    val value = res unwrap or_return: -1
    value * 2
expect parse_number_or_early() == -1
```

</details>

#### chaining and composition

#### can chain multiple unwrap operations

1. fn chain result
2. expect chain result
3. expect chain result
4. expect chain result
5. expect chain result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn chain_result(opt1, opt2):
    val v1 = opt1 unwrap or: 0
    val v2 = opt2 unwrap or: 0
    v1 + v2
expect chain_result(Some(10), Some(20)) == 30
expect chain_result(Some(10), None) == 10
expect chain_result(None, Some(20)) == 20
expect chain_result(None, None) == 0
```

</details>

#### works in nested expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(5)
val result = (opt unwrap or: 0) * 2 + 10
expect result == 20
```

</details>

#### type safety

#### preserves Option type semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_value: Option<text> = Some("hello")
val text_result = maybe_value unwrap or: "world"
expect text_result == "hello"
```

</details>

#### handles nested Option types

1. expect inner == Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested: Option<Option<i64>> = Some(Some(42))
# Unwraps outer layer
val inner = nested unwrap or: Some(0)
expect inner == Some(42)
```

</details>

#### preserves Result error information

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<i64, text> = Err("error message")
val recovered = result unwrap or: 0
expect recovered == 0
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
