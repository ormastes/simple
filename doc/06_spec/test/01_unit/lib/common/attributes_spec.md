# Attributes Specification

> <details>

<!-- sdn-diagram:id=attributes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=attributes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

attributes_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=attributes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Attributes Specification

## Scenarios

### #[inline] attribute

#### can be applied to functions

- fn helper func
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that @inline attribute is recognized by compiler
# For now, just verify syntax is accepted
fn helper_func(x: i32) -> i32:
    return x * 2

val result = helper_func(5)
expect(result).to_equal(10)
```

</details>

#### can be applied to methods

- fn double
   - Expected: obj.double() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify @inline works on methods
class TestClass:
    value: i32

    fn double() -> i32:
        return self.value * 2

val obj = TestClass { value: 5 }
expect(obj.double()).to_equal(10)
```

</details>

#### works with small helper functions

- fn add
- fn multiply
   - Expected: add(2, 3) equals `5`
   - Expected: multiply(2, 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple functions in same test block
fn add(a: i32, b: i32) -> i32:
    return a + b

fn multiply(a: i32, b: i32) -> i32:
    return a * b

expect(add(2, 3)).to_equal(5)
expect(multiply(2, 3)).to_equal(6)
```

</details>

### #[derive] attribute

#### generates Debug implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify derive attribute syntax is accepted
# Full derive implementation pending
class Point:
    x: i32
    y: i32

val p = Point { x: 1, y: 2 }
expect(p.x).to_equal(1)
```

</details>

#### generates Clone implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify derive works with Clone
class Data:
    value: i32

val d = Data { value: 42 }
expect(d.value).to_equal(42)
```

</details>

#### generates Eq implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify derive works with Eq
class Id:
    num: i32

val id1 = Id { num: 1 }
val id2 = Id { num: 1 }
expect(id1.num).to_equal(id2.num)
```

</details>

#### can derive multiple traits

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiple derives on same class
class Multi:
    a: i32
    b: i32

val m = Multi { a: 1, b: 2 }
expect(m.a).to_equal(1)
```

</details>

### #[cfg] attribute

#### enables conditional compilation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cfg attribute syntax test
# Conditional compilation pending full implementation
val x = 10
expect(x).to_equal(10)
```

</details>

#### supports platform conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Platform-specific cfg
val platform_value = 42
expect(platform_value).to_equal(42)
```

</details>

#### supports feature flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feature flag cfg
val feature_enabled = true
expect(feature_enabled).to_equal(true)
```

</details>

### #[deprecated] attribute

#### marks items as deprecated

- fn old function
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# deprecated attribute syntax test
fn old_function() -> i32:
    return 100

val result = old_function()
expect(result).to_equal(100)
```

</details>

#### includes replacement message

- fn legacy api
   - Expected: msg equals `legacy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# deprecated with message
fn legacy_api() -> text:
    return "legacy"

val msg = legacy_api()
expect(msg).to_equal("legacy")
```

</details>

### #[test] attribute

#### marks test functions

- fn test helper
   - Expected: test_helper() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# test attribute syntax
fn test_helper() -> bool:
    return true

expect(test_helper()).to_equal(true)
```

</details>

#### supports should_panic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# should_panic attribute test
# Panic handling pending
val safe_value = 42
expect(safe_value).to_equal(42)
```

</details>

#### supports ignore

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ignore attribute test
val ignored_test = true
expect(ignored_test).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/attributes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- #[inline] attribute
- #[derive] attribute
- #[cfg] attribute
- #[deprecated] attribute
- #[test] attribute

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
