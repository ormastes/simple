# RV32 Register File Unit Tests

> Unit tests for the 32x32 register file.

<!-- sdn-diagram:id=rv32_regfile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_regfile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_regfile_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_regfile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 Register File Unit Tests

Unit tests for the 32x32 register file.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-REGFILE-001 |
| Category | Hardware |
| Difficulty | 1/5 |
| Status | In Progress |
| Source | `test/01_unit/hardware/rv32imac/rv32_regfile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for the 32x32 register file.

## Scenarios

### Register File

#### initializes all registers to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rf = Rv32RegFile.create()
var i = 0
while i < 32:
    expect(rf.read(i)).to_equal(0)
    i = i + 1
```

</details>

#### x0 is hardwired to zero

1. var rf = Rv32RegFile create
2. rf write
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv32RegFile.create()
rf.write(0, 0xFFFFFFFF)
expect(rf.read(0)).to_equal(0)
```

</details>

#### writes to x1 through x31

1. var rf = Rv32RegFile create
2. rf write
3. rf write
4. rf write
   - Expected: rf.read(1) equals `0x11111111`
   - Expected: rf.read(15) equals `0x55555555`
   - Expected: rf.read(31) equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv32RegFile.create()
rf.write(1, 0x11111111)
rf.write(15, 0x55555555)
rf.write(31, 0xFFFFFFFF)
expect(rf.read(1)).to_equal(0x11111111)
expect(rf.read(15)).to_equal(0x55555555)
expect(rf.read(31)).to_equal(0xFFFFFFFF)
```

</details>

#### overwrites previous value

1. var rf = Rv32RegFile create
2. rf write
3. rf write
   - Expected: rf.read(5) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv32RegFile.create()
rf.write(5, 100)
rf.write(5, 200)
expect(rf.read(5)).to_equal(200)
```

</details>

#### masks to 32 bits

1. var rf = Rv32RegFile create
2. rf write
   - Expected: rf.read(1) equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv32RegFile.create()
rf.write(1, 0x1FFFFFFFF)
expect(rf.read(1)).to_equal(0xFFFFFFFF)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
