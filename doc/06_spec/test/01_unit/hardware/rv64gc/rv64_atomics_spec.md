# RV64 Atomics Unit Tests

> Unit tests for RV64A extension: LR/SC pairs and AMO operations.

<!-- sdn-diagram:id=rv64_atomics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_atomics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_atomics_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_atomics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Atomics Unit Tests

Unit tests for RV64A extension: LR/SC pairs and AMO operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-ATOMICS-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_atomics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for RV64A extension: LR/SC pairs and AMO operations.

## Scenarios

### LR.D / SC.D

#### LR.D/SC.D success: reserve then conditional store succeeds

1. var rs =  create rs
2. rs reserve
   - Expected: rs.check(0x80001000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = _create_rs()
rs.reserve(0x80001000)
expect(rs.check(0x80001000)).to_equal(true)
```

</details>

#### SC.D fails after intervening store (reservation cleared)

1. var rs =  create rs
2. rs reserve
3. rs clear
   - Expected: rs.check(0x80001000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = _create_rs()
rs.reserve(0x80001000)
rs.clear()
expect(rs.check(0x80001000)).to_equal(false)
```

</details>

#### SC.D fails on wrong address

1. var rs =  create rs
2. rs reserve
   - Expected: rs.check(0x80002000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = _create_rs()
rs.reserve(0x80001000)
expect(rs.check(0x80002000)).to_equal(false)
```

</details>

### AMO.D Operations

#### AMOADD.D: adds value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Add, 100, 50)
expect(result.old_value).to_equal(100)
expect(result.new_value).to_equal(150)
```

</details>

#### AMOSWAP.D: swaps value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Swap, 100, 200)
expect(result.old_value).to_equal(100)
expect(result.new_value).to_equal(200)
```

</details>

#### AMOAND.D: bitwise AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.And, 0xFF, 0x0F)
expect(result.old_value).to_equal(0xFF)
expect(result.new_value).to_equal(0x0F)
```

</details>

#### AMOOR.D: bitwise OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Or, 0xF0, 0x0F)
expect(result.old_value).to_equal(0xF0)
expect(result.new_value).to_equal(0xFF)
```

</details>

#### AMOXOR.D: bitwise XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Xor, 0xFF, 0x0F)
expect(result.old_value).to_equal(0xFF)
expect(result.new_value).to_equal(0xF0)
```

</details>

#### AMOMAX.D: signed maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Max, -10, 5)
expect(result.old_value).to_equal(-10)
expect(result.new_value).to_equal(5)
```

</details>

#### AMOMAXU.D: unsigned maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Maxu, 5, 0xFFFFFFFFFFFFFFFF)
expect(result.old_value).to_equal(5)
expect(result.new_value).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### AMOMIN.D: signed minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Min, 10, -5)
expect(result.old_value).to_equal(10)
expect(result.new_value).to_equal(-5)
```

</details>

#### AMOMINU.D: unsigned minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Minu, 0xFFFFFFFFFFFFFFFF, 5)
expect(result.old_value).to_equal(0xFFFFFFFFFFFFFFFF)
expect(result.new_value).to_equal(5)
```

</details>

### LR.W / SC.W (32-bit)

#### LR.W/SC.W: reserve and check word address

1. var rs =  create rs
2. rs reserve
   - Expected: rs.check(0x80001000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = _create_rs()
rs.reserve(0x80001000)
expect(rs.check(0x80001000)).to_equal(true)
```

</details>

#### SC.W fails after clear

1. var rs =  create rs
2. rs reserve
3. rs clear
   - Expected: rs.check(0x80001000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = _create_rs()
rs.reserve(0x80001000)
rs.clear()
expect(rs.check(0x80001000)).to_equal(false)
```

</details>

### AMO.W Operations (32-bit)

#### AMOADD.W: 32-bit add

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Add, 100, 50)
expect(result.old_value).to_equal(100)
expect(result.new_value).to_equal(150)
```

</details>

#### AMOSWAP.W: swap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Swap, 100, 200)
expect(result.new_value).to_equal(200)
```

</details>

#### AMOAND.W: bitwise AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.And, 0xFF, 0x0F)
expect(result.new_value).to_equal(0x0F)
```

</details>

#### AMOOR.W: bitwise OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Or, 0xF0, 0x0F)
expect(result.new_value).to_equal(0xFF)
```

</details>

#### AMOXOR.W: bitwise XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Xor, 0xFF, 0x0F)
expect(result.new_value).to_equal(0xF0)
```

</details>

#### AMOMAX.W: signed max

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Max, -10, 5)
expect(result.new_value).to_equal(5)
```

</details>

#### AMOMIN.W: signed min

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Min, 10, -5)
expect(result.new_value).to_equal(-5)
```

</details>

#### AMOMAXU.W: unsigned max

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Maxu, 5, 0xFFFFFFFF)
expect(result.new_value).to_equal(0xFFFFFFFF)
```

</details>

#### AMOMINU.W: unsigned min

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = amo_execute(AmoOp.Minu, 0xFFFFFFFF, 5)
expect(result.new_value).to_equal(5)
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
