# RV64 Register File Unit Tests

> Unit tests for the 32×64-bit integer register file. x0 is hardwired to zero; x1-x31 are read/write 64-bit registers.

<!-- sdn-diagram:id=rv64_regfile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_regfile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_regfile_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_regfile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Register File Unit Tests

Unit tests for the 32×64-bit integer register file. x0 is hardwired to zero; x1-x31 are read/write 64-bit registers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-REGFILE-001 |
| Category | Hardware |
| Difficulty | 1/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_regfile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for the 32×64-bit integer register file.
x0 is hardwired to zero; x1-x31 are read/write 64-bit registers.

## Scenarios

### Rv64RegFile Initialization

#### all registers initialized to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rf = Rv64RegFile.create()
expect(rf.read(0)).to_equal(0)
expect(rf.read(1)).to_equal(0)
expect(rf.read(31)).to_equal(0)
```

</details>

### Rv64RegFile x0 Hardwired Zero

#### x0 always returns 0 after write

1. var rf = Rv64RegFile create
2. rf write
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(0, 0xDEADBEEFCAFEBABE)
expect(rf.read(0)).to_equal(0)
```

</details>

### Rv64RegFile Read/Write

#### write and read x1

1. var rf = Rv64RegFile create
2. rf write
   - Expected: rf.read(1) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(1, 42)
expect(rf.read(1)).to_equal(42)
```

</details>

#### write and read x31

1. var rf = Rv64RegFile create
2. rf write
   - Expected: rf.read(31) equals `0x7FFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(31, 0x7FFFFFFFFFFFFFFF)
expect(rf.read(31)).to_equal(0x7FFFFFFFFFFFFFFF)
```

</details>

#### overwrite preserves latest value

1. var rf = Rv64RegFile create
2. rf write
3. rf write
   - Expected: rf.read(10) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(10, 100)
rf.write(10, 200)
expect(rf.read(10)).to_equal(200)
```

</details>

#### full 64-bit value preserved

1. var rf = Rv64RegFile create
2. rf write
   - Expected: rf.read(5) equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(5, 0xFFFFFFFFFFFFFFFF)
expect(rf.read(5)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### upper 32 bits stored correctly

1. var rf = Rv64RegFile create
2. rf write
   - Expected: rf.read(7) equals `0x100000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(7, 0x100000000)
expect(rf.read(7)).to_equal(0x100000000)
```

</details>

#### independent registers do not interfere

1. var rf = Rv64RegFile create
2. rf write
3. rf write
   - Expected: rf.read(1) equals `111`
   - Expected: rf.read(2) equals `222`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(1, 111)
rf.write(2, 222)
expect(rf.read(1)).to_equal(111)
expect(rf.read(2)).to_equal(222)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
