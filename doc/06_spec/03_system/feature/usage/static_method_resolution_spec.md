# Static Method Resolution

> Tests static method resolution and calling in interpreter mode. Uses ClassName.method() dot-access syntax which works in closures.

<!-- sdn-diagram:id=static_method_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_method_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_method_resolution_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_method_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Method Resolution

Tests static method resolution and calling in interpreter mode. Uses ClassName.method() dot-access syntax which works in closures.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RESOLVE-001 |
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/feature/usage/static_method_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests static method resolution and calling in interpreter mode.
Uses ClassName.method() dot-access syntax which works in closures.

## Syntax

```simple
class Point:
    x: i64
    y: i64
    static fn origin() -> Point:
        Point(x: 0, y: 0)
val p = Point.origin()
```

## Scenarios

### Static Method Resolution

#### Basic static method resolution

#### resolves simple static method call

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Calculator.add(3, 4)
expect(result).to_equal(7)
```

</details>

#### resolves static method with parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Calculator.multiply(5, 6)
expect(result).to_equal(30)
```

</details>

#### resolves static method returning object

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calc = Calculator.zero()
expect(calc.get_value()).to_equal(0)
```

</details>

#### Static vs instance method distinction

#### correctly resolves static method vs instance method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calc = Calculator.from_value(42)
expect(calc.get_value()).to_equal(42)
```

</details>

#### allows same name for static and instance methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Static returns i64, instance returns field
val sum = Calculator.add(10, 20)
val calc = Calculator.from_value(100)
expect(sum).to_equal(30)
expect(calc.get_value()).to_equal(100)
```

</details>

#### Static method chaining

#### chains static method call with instance method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Calculator.from_value(10).get_value()
expect(result).to_equal(10)
```

</details>

#### calls multiple static methods in sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Calculator.add(1, 2)
val b = Calculator.multiply(3, 4)
expect(a + b).to_equal(15)
```

</details>

#### Static methods calling other methods

#### static method calls another static method

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = MathUtils.max(10, 20)
val n = MathUtils.min(10, 20)
expect(m).to_equal(20)
expect(n).to_equal(10)
```

</details>

#### static method creates object and calls instance method

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calc = Calculator.from_value(99)
val v = calc.get_value()
expect(v).to_equal(99)
```

</details>

#### Static method in structs

#### resolves static method on struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = MathUtils.abs(0 - 42)
expect(a).to_equal(42)
```

</details>

#### resolves multiple static methods on struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clamped = MathUtils.clamp(150, 0, 100)
expect(clamped).to_equal(100)
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
