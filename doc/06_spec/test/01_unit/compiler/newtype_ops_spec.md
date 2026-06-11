# Newtype Auto-Derived Operators Specification

> Newtypes wrapping numeric primitives (i64, f64) auto-derive dunder methods for arithmetic (`__add__`, `__sub__`, `__mul__`, `__div__`) and comparison (`__eq__`, `__lt__`, `__gt__`) operators. This allows natural operator syntax (`a + b`, `a < b`) on newtype instances without manual boilerplate.

<!-- sdn-diagram:id=newtype_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=newtype_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

newtype_ops_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=newtype_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Newtype Auto-Derived Operators Specification

Newtypes wrapping numeric primitives (i64, f64) auto-derive dunder methods for arithmetic (`__add__`, `__sub__`, `__mul__`, `__div__`) and comparison (`__eq__`, `__lt__`, `__gt__`) operators. This allows natural operator syntax (`a + b`, `a < b`) on newtype instances without manual boilerplate.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-043 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/newtype_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Newtypes wrapping numeric primitives (i64, f64) auto-derive dunder methods
for arithmetic (`__add__`, `__sub__`, `__mul__`, `__div__`) and comparison
(`__eq__`, `__lt__`, `__gt__`) operators. This allows natural operator syntax
(`a + b`, `a < b`) on newtype instances without manual boilerplate.

## Syntax

```simple
newtype Width = i64
val a = Width(value: 3)
val b = Width(value: 4)
val c = a + b          # Width(value: 7)
val eq = a == b        # false
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| newtype | A distinct type wrapping a single underlying value |
| auto-derive | Dunder methods generated automatically for numeric wrappers |
| type safety | Width + Width = Width; prevents mixing Width with Height |

## Scenarios

### newtype i64 operators

### arithmetic

#### supports addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 3)
val b = Width(value: 4)
val c = a + b
expect(c.value).to_equal(7)
```

</details>

#### supports subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 10)
val b = Width(value: 3)
val c = a - b
expect(c.value).to_equal(7)
```

</details>

#### supports multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 3)
val b = Width(value: 4)
val c = a * b
expect(c.value).to_equal(12)
```

</details>

#### supports division

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 12)
val b = Width(value: 4)
val c = a / b
expect(c.value).to_equal(3)
```

</details>

### comparison

#### supports equality when equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 5)
val b = Width(value: 5)
expect(a == b).to_equal(true)
```

</details>

#### supports equality when not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 5)
val b = Width(value: 3)
expect(a == b).to_equal(false)
```

</details>

#### supports less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 3)
val b = Width(value: 5)
expect(a < b).to_equal(true)
```

</details>

#### supports less than when not less

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 5)
val b = Width(value: 3)
expect(a < b).to_equal(false)
```

</details>

#### supports greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 5)
val b = Width(value: 3)
expect(a > b).to_equal(true)
```

</details>

#### supports greater than when not greater

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 3)
val b = Width(value: 5)
expect(a > b).to_equal(false)
```

</details>

### edge cases

#### handles zero values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 0)
val b = Width(value: 0)
val c = a + b
expect(c.value).to_equal(0)
expect(a == b).to_equal(true)
```

</details>

#### handles negative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: -3)
val b = Width(value: 2)
val c = a + b
expect(c.value).to_equal(-1)
```

</details>

#### handles subtraction resulting in negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 3)
val b = Width(value: 10)
val c = a - b
expect(c.value).to_equal(-7)
```

</details>

### newtype f64 operators

### arithmetic

#### supports addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 1.5)
val b = Temperature(value: 2.5)
val c = a + b
expect(c.value).to_equal(4.0)
```

</details>

#### supports subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 10.5)
val b = Temperature(value: 3.5)
val c = a - b
expect(c.value).to_equal(7.0)
```

</details>

#### supports multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 2.5)
val b = Temperature(value: 4.0)
val c = a * b
expect(c.value).to_equal(10.0)
```

</details>

#### supports division

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 9.0)
val b = Temperature(value: 3.0)
val c = a / b
expect(c.value).to_equal(3.0)
```

</details>

### comparison

#### supports equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 36.6)
val b = Temperature(value: 36.6)
expect(a == b).to_equal(true)
```

</details>

#### supports less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 20.0)
val b = Temperature(value: 30.0)
expect(a < b).to_equal(true)
```

</details>

#### supports greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 30.0)
val b = Temperature(value: 20.0)
expect(a > b).to_equal(true)
```

</details>

### edge cases

#### handles zero values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: 0.0)
val b = Temperature(value: 0.0)
val c = a + b
expect(c.value).to_equal(0.0)
```

</details>

#### handles negative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Temperature(value: -10.5)
val b = Temperature(value: 5.5)
val c = a + b
expect(c.value).to_equal(-5.0)
```

</details>

### newtype type safety

#### Width operations produce Width

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Width(value: 3)
val b = Width(value: 4)
val c = a + b
expect(c.value).to_equal(7)
```

</details>

#### Height operations produce Height

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Height(value: 10)
val b = Height(value: 5)
val c = a + b
expect(c.value).to_equal(15)
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
