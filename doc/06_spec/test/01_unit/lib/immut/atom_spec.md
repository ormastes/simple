# Atom Specification

> <details>

<!-- sdn-diagram:id=atom_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=atom_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

atom_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=atom_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atom Specification

## Scenarios

### Atom

### creation

#### creates with initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Atom.new(42)
expect(a.deref()).to_equal(42)
```

</details>

#### starts at version 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Atom.new(0)
expect(a.version()).to_equal(0)
```

</details>

#### Atom__of is alias for Atom__new

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Atom.of("hello")
expect(a.deref()).to_equal("hello")
```

</details>

#### creates with nil initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Atom.new(nil)
expect(a.deref()).to_be_nil()
```

</details>

#### creates with string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Atom.new("test")
expect(a.deref()).to_equal("test")
```

</details>

### deref

#### reads the current value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Atom.new(100)
expect(a.deref()).to_equal(100)
```

</details>

#### returns same value on repeated reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Atom.new(77)
expect(a.deref()).to_equal(77)
expect(a.deref()).to_equal(77)
```

</details>

### swap

#### applies function and returns new value

1. var a = Atom new
   - Expected: result equals `15`
   - Expected: a.deref() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(10)
val result = a.swap(_1 + 5)
expect(result).to_equal(15)
expect(a.deref()).to_equal(15)
```

</details>

#### increments version on swap

1. var a = Atom new
2. a swap
   - Expected: a.version() equals `1`
3. a swap
   - Expected: a.version() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(0)
a.swap(_1 + 1)
expect(a.version()).to_equal(1)
a.swap(_1 + 1)
expect(a.version()).to_equal(2)
```

</details>

#### applies multiplication

1. var a = Atom new
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(5)
val result = a.swap(_1 * 3)
expect(result).to_equal(15)
```

</details>

#### applies identity function

1. var a = Atom new
   - Expected: result equals `42`
   - Expected: a.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(42)
val result = a.swap(\x: x)
expect(result).to_equal(42)
expect(a.version()).to_equal(1)
```

</details>

### reset

#### sets new value unconditionally

1. var a = Atom new
2. a reset
   - Expected: a.deref() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(1)
a.reset(99)
expect(a.deref()).to_equal(99)
```

</details>

#### increments version

1. var a = Atom new
2. a reset
   - Expected: a.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(0)
a.reset(42)
expect(a.version()).to_equal(1)
```

</details>

#### overwrites previous value

1. var a = Atom new
2. a reset
3. a reset
   - Expected: a.deref() equals `30`
   - Expected: a.version() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(10)
a.reset(20)
a.reset(30)
expect(a.deref()).to_equal(30)
expect(a.version()).to_equal(2)
```

</details>

#### can reset to nil

1. var a = Atom new
2. a reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(42)
a.reset(nil)
expect(a.deref()).to_be_nil()
```

</details>

### compare_and_set

#### succeeds when expected matches

1. var a = Atom new
   - Expected: ok is true
   - Expected: a.deref() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(10)
val ok = a.compare_and_set(10, 20)
expect(ok).to_equal(true)
expect(a.deref()).to_equal(20)
```

</details>

#### fails when expected does not match

1. var a = Atom new
   - Expected: ok is false
   - Expected: a.deref() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(10)
val ok = a.compare_and_set(5, 20)
expect(ok).to_equal(false)
expect(a.deref()).to_equal(10)
```

</details>

#### does not increment version on failure

1. var a = Atom new
2. a compare and set
   - Expected: a.version() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(10)
a.compare_and_set(999, 20)
expect(a.version()).to_equal(0)
```

</details>

#### increments version on success

1. var a = Atom new
2. a compare and set
   - Expected: a.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(10)
a.compare_and_set(10, 20)
expect(a.version()).to_equal(1)
```

</details>

### swap_returning_old

#### returns old value

1. var a = Atom new
   - Expected: old equals `100`
   - Expected: a.deref() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(100)
val old = a.swap_returning_old(_1 * 2)
expect(old).to_equal(100)
expect(a.deref()).to_equal(200)
```

</details>

#### increments version

1. var a = Atom new
2. a swap returning old
   - Expected: a.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(0)
a.swap_returning_old(_1 + 1)
expect(a.version()).to_equal(1)
```

</details>

#### returns old on multiple swaps

1. var a = Atom new
   - Expected: old1 equals `1`
   - Expected: old2 equals `11`
   - Expected: a.deref() equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(1)
val old1 = a.swap_returning_old(_1 + 10)
val old2 = a.swap_returning_old(_1 + 10)
expect(old1).to_equal(1)
expect(old2).to_equal(11)
expect(a.deref()).to_equal(21)
```

</details>

### multiple operations

#### tracks version across operations

1. var a = Atom new
2. a swap
3. a reset
4. a compare and set
   - Expected: a.version() equals `3`
   - Expected: a.deref() equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(0)
a.swap(_1 + 1)
a.reset(50)
a.compare_and_set(50, 100)
expect(a.version()).to_equal(3)
expect(a.deref()).to_equal(100)
```

</details>

#### failed CAS does not affect version

1. var a = Atom new
2. a swap
3. a compare and set
   - Expected: a.version() equals `1`
   - Expected: a.deref() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(0)
a.swap(_1 + 1)
a.compare_and_set(999, 0)
expect(a.version()).to_equal(1)
expect(a.deref()).to_equal(1)
```

</details>

#### sequence of resets

1. var a = Atom new
2. a reset
3. a reset
4. a reset
   - Expected: a.deref() equals `3`
   - Expected: a.version() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Atom.new(0)
a.reset(1)
a.reset(2)
a.reset(3)
expect(a.deref()).to_equal(3)
expect(a.version()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/immut/atom_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Atom
- creation
- deref
- swap
- reset
- compare_and_set
- swap_returning_old
- multiple operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
