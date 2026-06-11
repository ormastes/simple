# RV64 FP Register File Unit Tests

> Unit tests for 32×64-bit FP register file with NaN-boxing for F extension.

<!-- sdn-diagram:id=rv64_fp_regfile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_fp_regfile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_fp_regfile_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_fp_regfile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 FP Register File Unit Tests

Unit tests for 32×64-bit FP register file with NaN-boxing for F extension.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-FP-REGFILE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_fp_regfile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for 32×64-bit FP register file with NaN-boxing for F extension.

## Scenarios

### FP Register File Initialization

#### all FP registers initialized to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frf = Rv64FpuRegFile.create()
expect(frf.read(0)).to_equal(0)
expect(frf.read(31)).to_equal(0)
```

</details>

### FP Register Read/Write

#### write and read f1

1. var frf = Rv64FpuRegFile create
2. frf write
   - Expected: frf.read(1) equals `0x3FF0000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frf = Rv64FpuRegFile.create()
frf.write(1, 0x3FF0000000000000)
expect(frf.read(1)).to_equal(0x3FF0000000000000)
```

</details>

#### write and read f31

1. var frf = Rv64FpuRegFile create
2. frf write
   - Expected: frf.read(31) equals `0x4000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frf = Rv64FpuRegFile.create()
frf.write(31, 0x4000000000000000)
expect(frf.read(31)).to_equal(0x4000000000000000)
```

</details>

#### overwrite preserves latest

1. var frf = Rv64FpuRegFile create
2. frf write
3. frf write
   - Expected: frf.read(5) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frf = Rv64FpuRegFile.create()
frf.write(5, 100)
frf.write(5, 200)
expect(frf.read(5)).to_equal(200)
```

</details>

### NaN-Boxing

#### write_single NaN-boxes upper 32 bits

1. var frf = Rv64FpuRegFile create
2. frf write single
   - Expected: stored equals `0xFFFFFFFF3F800000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frf = Rv64FpuRegFile.create()
frf.write_single(1, 0x3F800000)
val stored = frf.read(1)
expect(stored).to_equal(0xFFFFFFFF3F800000)
```

</details>

#### read_single extracts lower 32 bits when NaN-boxed

1. var frf = Rv64FpuRegFile create
2. frf write single
   - Expected: frf.read_single(1) equals `0x3F800000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frf = Rv64FpuRegFile.create()
frf.write_single(1, 0x3F800000)
expect(frf.read_single(1)).to_equal(0x3F800000)
```

</details>

#### read_single returns canonical NaN when not NaN-boxed

1. var frf = Rv64FpuRegFile create
2. frf write
   - Expected: frf.read_single(1) equals `0x7FC00000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frf = Rv64FpuRegFile.create()
frf.write(1, 0x0000000000000000)
expect(frf.read_single(1)).to_equal(0x7FC00000)
```

</details>

#### double-precision values stored directly

1. var frf = Rv64FpuRegFile create
2. frf write
   - Expected: frf.read(1) equals `0x3FF0000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frf = Rv64FpuRegFile.create()
frf.write(1, 0x3FF0000000000000)
expect(frf.read(1)).to_equal(0x3FF0000000000000)
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
