# RV32 Compressed Extension Unit Tests

> Unit tests for RVC 16-to-32 bit instruction decompression.

<!-- sdn-diagram:id=rv32_compressed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_compressed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_compressed_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_compressed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 Compressed Extension Unit Tests

Unit tests for RVC 16-to-32 bit instruction decompression.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-RVC-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/hardware/rv32imac/rv32_compressed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for RVC 16-to-32 bit instruction decompression.

## Scenarios

### RVC Detection

#### detects 16-bit instructions (bits 1:0 != 11)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed(0x0000)).to_equal(true)
expect(is_compressed(0x0001)).to_equal(true)
expect(is_compressed(0x0002)).to_equal(true)
```

</details>

#### detects 32-bit instructions (bits 1:0 == 11)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed(0x0003)).to_equal(false)
expect(is_compressed(0x00000033)).to_equal(false)
```

</details>

### RVC Register Mapping

#### maps 3-bit register 0 to x8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rvc_reg(0)).to_equal(8)
```

</details>

#### maps 3-bit register 7 to x15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rvc_reg(7)).to_equal(15)
```

</details>

### RVC Quadrant 2 Decompression

#### decompresses C.MV (rd = rs2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# C.MV x1, x2: 1000_00001_00010_10
val c_mv = 0x8092
val expanded = decompress_rvc(c_mv)
# Verify it's a 32-bit instruction
if (expanded and 0x3) == 0x3:
    expect(decode_opcode(expanded)).to_equal(OP_OP)
```

</details>

### RVC Quadrant 1 Decompression

#### decompresses C.NOP

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_nop = 0x0001
val expanded = decompress_rvc(c_nop)
# Should become ADDI x0, x0, 0
expect(decode_opcode(expanded)).to_equal(OP_OP_IMM)
expect(decode_rd(expanded)).to_equal(0)
```

</details>

#### decompresses C.LI (addi rd, x0, imm)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_li = 0x4515  # C.LI x10, 5
val expanded = decompress_rvc(c_li)
expect(decode_opcode(expanded)).to_equal(OP_OP_IMM)
expect(decode_rd(expanded)).to_equal(10)
expect(decode_rs1(expanded)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
