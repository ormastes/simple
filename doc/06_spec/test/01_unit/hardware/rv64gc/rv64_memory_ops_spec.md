# RV64 Memory Operations Unit Tests

> Unit tests for all load/store variants: LB, LH, LW, LD, LBU, LHU, LWU, SB, SH, SW, SD. Tests byte-level memory access with sign/zero extension.

<!-- sdn-diagram:id=rv64_memory_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_memory_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_memory_ops_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_memory_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Memory Operations Unit Tests

Unit tests for all load/store variants: LB, LH, LW, LD, LBU, LHU, LWU, SB, SH, SW, SD. Tests byte-level memory access with sign/zero extension.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-MEMOPS-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_memory_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for all load/store variants: LB, LH, LW, LD, LBU, LHU, LWU,
SB, SH, SW, SD. Tests byte-level memory access with sign/zero extension.

## Scenarios

### SB (Store Byte)

#### stores lowest byte

1. var ram = Rv64Ram create
2. ram write8
   - Expected: ram.read8(0).value equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0xAB)
expect(ram.read8(0).value).to_equal(0xAB)
```

</details>

#### stores only lower 8 bits

1. var ram = Rv64Ram create
2. ram write8
   - Expected: ram.read8(0).value equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0x1AB)
expect(ram.read8(0).value).to_equal(0xAB)
```

</details>

#### stores to specific address

1. var ram = Rv64Ram create
2. ram write8
   - Expected: ram.read8(5).value equals `0xFF`
   - Expected: ram.read8(4).value equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(5, 0xFF)
expect(ram.read8(5).value).to_equal(0xFF)
expect(ram.read8(4).value).to_equal(0x00)
```

</details>

### SH (Store Halfword)

#### stores 16-bit little-endian

1. var ram = Rv64Ram create
2. ram write16
   - Expected: ram.read8(0).value equals `0xEF`
   - Expected: ram.read8(1).value equals `0xBE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write16(0, 0xBEEF)
expect(ram.read8(0).value).to_equal(0xEF)
expect(ram.read8(1).value).to_equal(0xBE)
```

</details>

#### read16 returns correct value

1. var ram = Rv64Ram create
2. ram write16
   - Expected: ram.read16(2).value equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write16(2, 0x1234)
expect(ram.read16(2).value).to_equal(0x1234)
```

</details>

### SW (Store Word)

#### stores 32-bit little-endian

1. var ram = Rv64Ram create
2. ram write32
   - Expected: ram.read32(0).value equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0xDEADBEEF)
expect(ram.read32(0).value).to_equal(0xDEADBEEF)
```

</details>

#### bytes stored in correct order

1. var ram = Rv64Ram create
2. ram write32
   - Expected: ram.read8(0).value equals `0x01`
   - Expected: ram.read8(1).value equals `0x02`
   - Expected: ram.read8(2).value equals `0x03`
   - Expected: ram.read8(3).value equals `0x04`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0x04030201)
expect(ram.read8(0).value).to_equal(0x01)
expect(ram.read8(1).value).to_equal(0x02)
expect(ram.read8(2).value).to_equal(0x03)
expect(ram.read8(3).value).to_equal(0x04)
```

</details>

### SD (Store Doubleword)

#### stores 64-bit little-endian

1. var ram = Rv64Ram create
2. ram write64
   - Expected: ram.read64(0).value equals `0xDEADBEEFCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write64(0, 0xDEADBEEFCAFEBABE)
expect(ram.read64(0).value).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### bytes stored in correct order

1. var ram = Rv64Ram create
2. ram write64
   - Expected: ram.read8(0).value equals `0x01`
   - Expected: ram.read8(7).value equals `0x08`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write64(0, 0x0807060504030201)
expect(ram.read8(0).value).to_equal(0x01)
expect(ram.read8(7).value).to_equal(0x08)
```

</details>

### LB (Load Byte — sign-extended)

#### LB positive byte

1. var ram = Rv64Ram create
2. ram write8
   - Expected: _sign_extend_8(raw) equals `0x7F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0x7F)
val raw = ram.read8(0).value
expect(_sign_extend_8(raw)).to_equal(0x7F)
```

</details>

#### LB negative byte sign-extends to 64 bits

1. var ram = Rv64Ram create
2. ram write8
   - Expected: _sign_extend_8(raw) equals `0xFFFFFFFFFFFFFF80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0x80)
val raw = ram.read8(0).value
expect(_sign_extend_8(raw)).to_equal(0xFFFFFFFFFFFFFF80)
```

</details>

#### LB 0xFF sign-extends to -1

1. var ram = Rv64Ram create
2. ram write8
   - Expected: _sign_extend_8(raw) equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0xFF)
val raw = ram.read8(0).value
expect(_sign_extend_8(raw)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### LBU (Load Byte Unsigned — zero-extended)

#### LBU positive byte

1. var ram = Rv64Ram create
2. ram write8
   - Expected: ram.read8(0).value equals `0x7F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0x7F)
expect(ram.read8(0).value).to_equal(0x7F)
```

</details>

#### LBU high byte stays unsigned

1. var ram = Rv64Ram create
2. ram write8
   - Expected: ram.read8(0).value equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0xFF)
expect(ram.read8(0).value).to_equal(0xFF)
```

</details>

#### LBU 0x80 stays positive

1. var ram = Rv64Ram create
2. ram write8
   - Expected: ram.read8(0).value equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0x80)
expect(ram.read8(0).value).to_equal(0x80)
```

</details>

### LH (Load Halfword — sign-extended)

#### LH positive halfword

1. var ram = Rv64Ram create
2. ram write16
   - Expected: _sign_extend_16(raw) equals `0x7FFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write16(0, 0x7FFF)
val raw = ram.read16(0).value
expect(_sign_extend_16(raw)).to_equal(0x7FFF)
```

</details>

#### LH negative halfword sign-extends

1. var ram = Rv64Ram create
2. ram write16
   - Expected: _sign_extend_16(raw) equals `0xFFFFFFFFFFFF8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write16(0, 0x8000)
val raw = ram.read16(0).value
expect(_sign_extend_16(raw)).to_equal(0xFFFFFFFFFFFF8000)
```

</details>

#### LH 0xFFFF sign-extends to -1

1. var ram = Rv64Ram create
2. ram write16
   - Expected: _sign_extend_16(raw) equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write16(0, 0xFFFF)
val raw = ram.read16(0).value
expect(_sign_extend_16(raw)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### LHU (Load Halfword Unsigned)

#### LHU stays unsigned

1. var ram = Rv64Ram create
2. ram write16
   - Expected: ram.read16(0).value equals `0xFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write16(0, 0xFFFF)
expect(ram.read16(0).value).to_equal(0xFFFF)
```

</details>

#### LHU 0x8000 stays positive

1. var ram = Rv64Ram create
2. ram write16
   - Expected: ram.read16(0).value equals `0x8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write16(0, 0x8000)
expect(ram.read16(0).value).to_equal(0x8000)
```

</details>

### LW (Load Word — sign-extended)

#### LW positive word

1. var ram = Rv64Ram create
2. ram write32
   - Expected: _sign_extend_32(raw) equals `0x7FFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0x7FFFFFFF)
val raw = ram.read32(0).value
expect(_sign_extend_32(raw)).to_equal(0x7FFFFFFF)
```

</details>

#### LW negative word sign-extends

1. var ram = Rv64Ram create
2. ram write32
   - Expected: _sign_extend_32(raw) equals `0xFFFFFFFF80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0x80000000)
val raw = ram.read32(0).value
expect(_sign_extend_32(raw)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### LW 0xFFFFFFFF sign-extends to -1

1. var ram = Rv64Ram create
2. ram write32
   - Expected: _sign_extend_32(raw) equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0xFFFFFFFF)
val raw = ram.read32(0).value
expect(_sign_extend_32(raw)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### LWU (Load Word Unsigned)

#### LWU stays unsigned

1. var ram = Rv64Ram create
2. ram write32
   - Expected: ram.read32(0).value equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0xFFFFFFFF)
expect(ram.read32(0).value).to_equal(0xFFFFFFFF)
```

</details>

#### LWU 0x80000000 stays positive

1. var ram = Rv64Ram create
2. ram write32
   - Expected: ram.read32(0).value equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0x80000000)
expect(ram.read32(0).value).to_equal(0x80000000)
```

</details>

### LD (Load Doubleword)

#### LD full 64-bit value

1. var ram = Rv64Ram create
2. ram write64
   - Expected: ram.read64(0).value equals `0xDEADBEEFCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write64(0, 0xDEADBEEFCAFEBABE)
expect(ram.read64(0).value).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### LD zero

1. var ram = Rv64Ram create
   - Expected: ram.read64(0).value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
expect(ram.read64(0).value).to_equal(0)
```

</details>

### Out-of-Bounds Access

#### read beyond bounds returns fault

1. var ram = Rv64Ram create
   - Expected: result.fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(8)
val result = ram.read8(8)
expect(result.fault).to_equal(true)
```

</details>

#### write beyond bounds returns fault

1. var ram = Rv64Ram create
   - Expected: result.fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(8)
val result = ram.write8(8, 0xFF)
expect(result.fault).to_equal(true)
```

</details>

#### 64-bit access at boundary faults

1. var ram = Rv64Ram create
   - Expected: result.fault is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(8)
val result = ram.read64(1)
expect(result.fault).to_equal(true)
```

</details>

### Mixed Width Operations

#### write word then read bytes

1. var ram = Rv64Ram create
2. ram write32
   - Expected: ram.read8(0).value equals `0xEF`
   - Expected: ram.read8(1).value equals `0xBE`
   - Expected: ram.read8(2).value equals `0xAD`
   - Expected: ram.read8(3).value equals `0xDE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write32(0, 0xDEADBEEF)
expect(ram.read8(0).value).to_equal(0xEF)
expect(ram.read8(1).value).to_equal(0xBE)
expect(ram.read8(2).value).to_equal(0xAD)
expect(ram.read8(3).value).to_equal(0xDE)
```

</details>

#### write bytes then read word

1. var ram = Rv64Ram create
2. ram write8
3. ram write8
4. ram write8
5. ram write8
   - Expected: ram.read32(0).value equals `0x04030201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write8(0, 0x01)
ram.write8(1, 0x02)
ram.write8(2, 0x03)
ram.write8(3, 0x04)
expect(ram.read32(0).value).to_equal(0x04030201)
```

</details>

#### write double then read words

1. var ram = Rv64Ram create
2. ram write64
   - Expected: ram.read32(0).value equals `0xDEADBEEF`
   - Expected: ram.read32(4).value equals `0xCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ram = Rv64Ram.create(16)
ram.write64(0, 0xCAFEBABEDEADBEEF)
expect(ram.read32(0).value).to_equal(0xDEADBEEF)
expect(ram.read32(4).value).to_equal(0xCAFEBABE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
