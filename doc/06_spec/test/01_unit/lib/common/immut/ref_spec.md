# Ref Specification

> <details>

<!-- sdn-diagram:id=ref_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ref_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ref_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ref_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ref Specification

## Scenarios

### Ref

### creation

#### creates with valid initial value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(10, _1 > 0)
expect(r.deref()).to_equal(10)
```

</details>

#### returns nil when initial value fails validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(-5, _1 > 0)
expect(r).to_be_nil()
```

</details>

#### creates with zero when validator accepts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(0, _1 >= 0)
expect(r.deref()).to_equal(0)
```

</details>

#### Ref__of is alias for Ref__new

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.of(42, _1 > 0)
expect(r.deref()).to_equal(42)
```

</details>

#### Ref__of returns nil on invalid initial

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.of(-1, _1 > 0)
expect(r).to_be_nil()
```

</details>

#### Ref__unvalidated creates without constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.unvalidated(0)
expect(r.deref()).to_equal(0)
```

</details>

#### Ref__unvalidated accepts any value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.unvalidated(-999)
expect(r.deref()).to_equal(-999)
```

</details>

#### Ref__unvalidated accepts nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.unvalidated(nil)
expect(r.deref()).to_be_nil()
```

</details>

### deref

#### returns current value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(100, _1 > 0)
expect(r.deref()).to_equal(100)
```

</details>

#### returns same value on repeated reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(55, _1 > 0)
expect(r.deref()).to_equal(55)
expect(r.deref()).to_equal(55)
```

</details>

### version

#### starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(1, _1 > 0)
expect(r.version()).to_equal(0)
```

</details>

#### unvalidated also starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.unvalidated(42)
expect(r.version()).to_equal(0)
```

</details>

### is_valid

#### returns true for valid value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(10, _1 > 0)
expect(r.is_valid(5)).to_equal(true)
```

</details>

#### returns false for invalid value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(10, _1 > 0)
expect(r.is_valid(-1)).to_equal(false)
```

</details>

#### does not modify the ref

1. r is valid
   - Expected: r.deref() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ref.new(10, _1 > 0)
r.is_valid(999)
expect(r.deref()).to_equal(10)
```

</details>

### swap

#### applies function when result is valid

1. var r = Ref new
   - Expected: result equals `15`
   - Expected: r.deref() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val result = r.swap(_1 + 5)
expect(result).to_equal(15)
expect(r.deref()).to_equal(15)
```

</details>

#### returns old value when result is invalid

1. var r = Ref new
   - Expected: result equals `10`
   - Expected: r.deref() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val result = r.swap(_1 - 100)
expect(result).to_equal(10)
expect(r.deref()).to_equal(10)
```

</details>

#### increments version on valid swap

1. var r = Ref new
2. r swap
   - Expected: r.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(1, _1 > 0)
r.swap(_1 + 1)
expect(r.version()).to_equal(1)
```

</details>

#### does not increment version on invalid swap

1. var r = Ref new
2. r swap
   - Expected: r.version() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(5, _1 > 0)
r.swap(_1 - 100)
expect(r.version()).to_equal(0)
```

</details>

#### identity function succeeds

1. var r = Ref new
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(42, _1 > 0)
val result = r.swap(\x: x)
expect(result).to_equal(42)
```

</details>

### reset

#### sets new value when valid

1. var r = Ref new
   - Expected: result equals `99`
   - Expected: r.deref() equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val result = r.reset(99)
expect(result).to_equal(99)
expect(r.deref()).to_equal(99)
```

</details>

#### returns current value when invalid

1. var r = Ref new
   - Expected: result equals `10`
   - Expected: r.deref() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val result = r.reset(-5)
expect(result).to_equal(10)
expect(r.deref()).to_equal(10)
```

</details>

#### increments version on valid reset

1. var r = Ref new
2. r reset
   - Expected: r.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(1, _1 > 0)
r.reset(50)
expect(r.version()).to_equal(1)
```

</details>

#### does not increment version on invalid reset

1. var r = Ref new
2. r reset
   - Expected: r.version() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(1, _1 > 0)
r.reset(-1)
expect(r.version()).to_equal(0)
```

</details>

### compare_and_set

#### succeeds when expected matches and value is valid

1. var r = Ref new
   - Expected: ok is true
   - Expected: r.deref() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val ok = r.compare_and_set(10, 20)
expect(ok).to_equal(true)
expect(r.deref()).to_equal(20)
```

</details>

#### fails when expected does not match

1. var r = Ref new
   - Expected: ok is false
   - Expected: r.deref() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val ok = r.compare_and_set(5, 20)
expect(ok).to_equal(false)
expect(r.deref()).to_equal(10)
```

</details>

#### fails when new value is invalid

1. var r = Ref new
   - Expected: ok is false
   - Expected: r.deref() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val ok = r.compare_and_set(10, -5)
expect(ok).to_equal(false)
expect(r.deref()).to_equal(10)
```

</details>

#### increments version on success

1. var r = Ref new
2. r compare and set
   - Expected: r.version() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
r.compare_and_set(10, 20)
expect(r.version()).to_equal(1)
```

</details>

#### does not increment version on failure

1. var r = Ref new
2. r compare and set
   - Expected: r.version() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
r.compare_and_set(10, -1)
expect(r.version()).to_equal(0)
```

</details>

### swap_validated

#### returns success pair on valid transition

1. var r = Ref new
   - Expected: result[0] is true
   - Expected: result[1] equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val result = r.swap_validated(_1 * 2)
expect(result[0]).to_equal(true)
expect(result[1]).to_equal(20)
```

</details>

#### returns failure pair on invalid transition

1. var r = Ref new
   - Expected: result[0] is false
   - Expected: result[1] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(10, _1 > 0)
val result = r.swap_validated(_1 - 100)
expect(result[0]).to_equal(false)
expect(result[1]).to_equal(10)
```

</details>

#### updates deref on success

1. var r = Ref new
2. r swap validated
   - Expected: r.deref() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(5, _1 > 0)
r.swap_validated(_1 + 10)
expect(r.deref()).to_equal(15)
```

</details>

#### preserves deref on failure

1. var r = Ref new
2. r swap validated
   - Expected: r.deref() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(5, _1 > 0)
r.swap_validated(_1 - 100)
expect(r.deref()).to_equal(5)
```

</details>

### multiple operations

#### tracks version across valid transitions

1. var r = Ref new
2. r swap
3. r reset
4. r compare and set
   - Expected: r.version() equals `3`
   - Expected: r.deref() equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(1, _1 > 0)
r.swap(_1 + 1)
r.reset(10)
r.compare_and_set(10, 20)
expect(r.version()).to_equal(3)
expect(r.deref()).to_equal(20)
```

</details>

#### rejected transitions do not advance version

1. var r = Ref new
2. r swap
3. r reset
4. r compare and set
   - Expected: r.version() equals `0`
   - Expected: r.deref() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.new(5, _1 > 0)
r.swap(_1 - 100)
r.reset(-1)
r.compare_and_set(5, -10)
expect(r.version()).to_equal(0)
expect(r.deref()).to_equal(5)
```

</details>

### unvalidated

#### swap always succeeds

1. var r = Ref unvalidated
   - Expected: result equals `-90`
   - Expected: r.deref() equals `-90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.unvalidated(10)
val result = r.swap(_1 - 100)
expect(result).to_equal(-90)
expect(r.deref()).to_equal(-90)
```

</details>

#### reset always succeeds

1. var r = Ref unvalidated
2. r reset
   - Expected: r.deref() equals `-999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.unvalidated(0)
r.reset(-999)
expect(r.deref()).to_equal(-999)
```

</details>

#### compare_and_set succeeds when expected matches

1. var r = Ref unvalidated
   - Expected: ok is true
   - Expected: r.deref() equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ref.unvalidated(10)
val ok = r.compare_and_set(10, -5)
expect(ok).to_equal(true)
expect(r.deref()).to_equal(-5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/immut/ref_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ref
- creation
- deref
- version
- is_valid
- swap
- reset
- compare_and_set
- swap_validated
- multiple operations
- unvalidated

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
