# Null Coalescing and Try Operator Parser Specification

> Tests for the `??` (null coalescing) and `?` (try) operators in various contexts. These operators should work correctly in:

<!-- sdn-diagram:id=null_coalescing_try_operator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=null_coalescing_try_operator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

null_coalescing_try_operator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=null_coalescing_try_operator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Null Coalescing and Try Operator Parser Specification

Tests for the `??` (null coalescing) and `?` (try) operators in various contexts. These operators should work correctly in:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-NULL-001 |
| Category | Parser / Operators |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/null_coalescing_try_operator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the `??` (null coalescing) and `?` (try) operators in various contexts.
These operators should work correctly in:
- Simple expressions
- Return statements
- For loop bodies
- If expression bodies
- Match arms

## Known Issues

The following patterns cause parse errors:
1. `val x = expr ?? return Err(...)` - "expected expression, found Return"
2. `val x = expr?` inside for loop body - may cause issues
3. `val x = if cond: Some(fn()?) else: None` - "expected identifier, found Val"

## Workarounds

Use explicit if/else or match instead of operators in these contexts.

## Scenarios

### Null Coalescing Operator (??)

#### simple expressions

#### returns left value when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: i64? = Some(42)
val result = opt ?? 0
expect(result).to_equal(42)
```

</details>

#### returns right value when None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: i64? = None
val result = opt ?? 99
expect(result).to_equal(99)
```

</details>

#### chains multiple coalescing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: i64? = None
val b: i64? = None
val c: i64? = Some(10)
val result = a ?? b ?? c ?? 0
expect(result).to_equal(10)
```

</details>

#### with function calls

#### evaluates right side lazily

1. fn increment
   - Expected: result equals `5`
   - Expected: counter equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var counter = 0
fn increment() -> i64:
    counter = counter + 1
    counter

val opt: i64? = Some(5)
val result = opt ?? increment()
expect(result).to_equal(5)
expect(counter).to_equal(0)
```

</details>

#### calls right side when None

1. fn fallback value
   - Expected: result equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn fallback_value() -> i64:
    99

val opt: i64? = None
val result = opt ?? fallback_value()
expect(result).to_equal(99)
```

</details>

### Try Operator (?)

#### with Result type

#### unwraps Ok value

1. fn get ok
2. Ok
3. fn use ok
4. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_ok() -> Result<i64, text>:
    Ok(42)

fn use_ok() -> Result<i64, text>:
    val x = get_ok()?
    Ok(x + 1)

val result = use_ok()
match result:
    case Ok(v): expect(v).to_equal(43)
    case Err(_): fail("Expected Ok")
```

</details>

#### propagates Err

1. fn get err
2. Err
3. fn use err
4. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_err() -> Result<i64, text>:
    Err("error")

fn use_err() -> Result<i64, text>:
    val x = get_err()?
    Ok(x + 1)

val result = use_err()
match result:
    case Ok(_): fail("Expected Err")
    case Err(e): expect(e).to_equal("error")
```

</details>

#### with Option type

#### unwraps Some value

1. fn get some
2. Some
3. fn use some
4. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_some() -> i64?:
    Some(42)

fn use_some() -> i64?:
    val x = get_some()?
    Some(x + 1)

val result = use_some()
match result:
    case Some(v): expect(v).to_equal(43)
    case None: fail("Expected Some")
```

</details>

#### propagates None

1. fn get none
2. fn use none
3. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_none() -> i64?:
    None

fn use_none() -> i64?:
    val x = get_none()?
    Some(x + 1)

val result = use_none()
var saw_none = false
match result:
    case Some(_): fail("Expected None")
    case None: saw_none = true
expect(saw_none)
```

</details>

### Parser Edge Cases

#### workaround patterns

#### explicit if/else instead of ?? return

1. fn parse value
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn parse_value(s: text) -> Result<i64, text>:
    val opt = s.parse_int()
    if not opt.?:
        return Err("parse failed")
    val value = opt ?? 0
    Ok(value)

val result = parse_value("42")
match result:
    case Ok(v): expect(v).to_equal(42)
    case Err(_): fail("Expected Ok")
```

</details>

<details>
<summary>Advanced: match instead of ? in for loop</summary>

#### match instead of ? in for loop

1. fn sum parsed
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_parsed(items: [text]) -> Result<i64, text>:
    var total = 0
    for item in items:
        val result = item.parse_int()
        match result:
            case Some(n): total = total + n
            case None: return Err("parse failed: {item}")
    Ok(total)

val result = sum_parsed(["1", "2", "3"])
match result:
    case Ok(v): expect(v).to_equal(6)
    case Err(_): fail("Expected Ok")
```

</details>


</details>

#### explicit match for optional config

1. fn parse timeout
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Workaround: use simple text parsing instead of Dict (generics not supported at runtime)
fn parse_timeout(timeout_str: text) -> Result<i64, text>:
    var timeout: i64? = None
    val parsed = timeout_str.parse_int()
    match parsed:
        case Some(t): timeout = Some(t)
        case None: return Err("invalid timeout")
    Ok(timeout ?? 30)

val result = parse_timeout("60")
match result:
    case Ok(v): expect(v).to_equal(60)
    case Err(_): fail("Expected Ok")
```

</details>

#### previously reported bugs (now fixed)

#### ? in if-expression body

1. fn parse int result
2. Ok
3. fn parse optional
4. Some
5. Ok
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn parse_int_result(s: text) -> Result<i64, text>:
    val parsed = s.parse_int()
    if not parsed.?:
        return Err("parse failed")
    Ok(parsed ?? 0)

fn parse_optional(has_value: bool, s: text) -> Result<i64?, text>:
    val result = if has_value:
        Some(parse_int_result(s)?)
    else:
        None
    Ok(result)

val r1 = parse_optional(true, "42")
match r1:
    case Ok(v): expect(v ?? 0).to_equal(42)
    case Err(_): fail("Expected Ok")

val r2 = parse_optional(false, "")
match r2:
    case Ok(v):
        val is_none = not v.?
        expect(is_none).to_equal(true)
    case Err(_): fail("Expected Ok")
```

</details>

<details>
<summary>Advanced: ? in for loop with Result</summary>

#### ? in for loop with Result

1. fn parse int result
2. Ok
3. fn sum parsed
4. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn parse_int_result(s: text) -> Result<i64, text>:
    val parsed = s.parse_int()
    if not parsed.?:
        return Err("parse failed: {s}")
    Ok(parsed ?? 0)

fn sum_parsed(items: [text]) -> Result<i64, text>:
    var total = 0
    for item in items:
        val n = parse_int_result(item)?
        total = total + n
    Ok(total)

val r1 = sum_parsed(["1", "2", "3"])
match r1:
    case Ok(v): expect(v).to_equal(6)
    case Err(_): fail("Expected Ok")

val r2 = sum_parsed(["1", "abc", "3"])
match r2:
    case Ok(_): fail("Expected Err")
    case Err(e): expect(e).to_equal("parse failed: abc")
```

</details>


</details>

#### known parser bugs

#### ?? return Err pattern

1. fn parse with default
2. Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BUG: Bootstrap parser error "expected expression, found Return"
# Root cause: bootstrap binary's parse_primary_expr() doesn't handle
# KwReturn in expression position. Source fix exists in both
# src/compiler/parser.spl and src/app/parser/expr/postfix.spl
# but requires bootstrap rebuild to take effect.
# Workaround: use explicit if/else instead of ?? return
fn parse_with_default(s: text) -> Result<i64, text>:
    val opt = s.parse_int()
    if not opt.?:
        return Err("parse failed")
    Ok(opt ?? 0)

val result = parse_with_default("42")
match result:
    case Ok(v): expect(v).to_equal(42)
    case Err(_): expect("should not error").to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
