# RV64 Compressed Instructions Unit Tests

> Unit tests for RV64C compressed instruction detection and decompression. 16-bit instructions expand to 32-bit equivalents.

<!-- sdn-diagram:id=rv64_compressed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_compressed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_compressed_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_compressed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Compressed Instructions Unit Tests

Unit tests for RV64C compressed instruction detection and decompression. 16-bit instructions expand to 32-bit equivalents.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-COMPRESSED-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_compressed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for RV64C compressed instruction detection and decompression.
16-bit instructions expand to 32-bit equivalents.

## Scenarios

### Compressed Detection

#### 16-bit instruction detected (bits 1:0 = 00)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed(0x4000)).to_equal(true)
```

</details>

#### 32-bit instruction not compressed (bits 1:0 = 11)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed(0x00A00513)).to_equal(false)
```

</details>

### Register Mapping

#### rvc_reg(0) = 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rvc_reg(0)).to_equal(8)
```

</details>

#### rvc_reg(7) = 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rvc_reg(7)).to_equal(15)
```

</details>

### Quadrant 0 Decompression

#### C.ADDI4SPN: expands to ADDI rd', x2, nzuimm

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# C.ADDI4SPN x8, sp, 16 => ADDI x8, x2, 16
val compressed = 0x0040  # C.ADDI4SPN rd'=0(x8), nzuimm=16
val expanded = decompress_rvc(compressed)
# Verify opcode is OP_IMM (0x13)
expect(expanded and 0x7F).to_equal(0x13)
```

</details>

#### C.LW: expands to LW rd', offset(rs1')

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x4188  # C.LW
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD opcode
```

</details>

#### C.LD: expands to LD rd', offset(rs1') (RV64 only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x6188  # C.LD
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD opcode
```

</details>

#### C.SD: expands to SD rs2', offset(rs1') (RV64 only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0xE188  # C.SD
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x23)  # STORE opcode
```

</details>

### Quadrant 1 Decompression

#### C.NOP: expands to ADDI x0, x0, 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x0001  # C.NOP
val expanded = decompress_rvc(compressed)
expect(expanded).to_equal(0x00000013)  # ADDI x0, x0, 0
```

</details>

#### C.ADDI: expands to ADDI rd, rd, nzimm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x0505  # C.ADDI x10, 1
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x13)  # OP_IMM
```

</details>

#### C.ADDIW: expands to ADDIW rd, rd, imm (RV64 only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x2505  # C.ADDIW x10, 1
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x1B)  # OP_IMM_32
```

</details>

#### C.J: expands to JAL x0, offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0xA001  # C.J offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x6F)  # JAL
```

</details>

#### C.BEQZ: expands to BEQ rs1', x0, offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0xC001  # C.BEQZ
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x63)  # BRANCH
```

</details>

#### C.BNEZ: expands to BNE rs1', x0, offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0xE001  # C.BNEZ
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x63)  # BRANCH
```

</details>

### Quadrant 2 Decompression

#### C.SLLI: expands to SLLI rd, rd, shamt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x0502  # C.SLLI x10, 1 (approx encoding)
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x13)  # OP_IMM
```

</details>

#### C.LDSP: expands to LD rd, offset(x2) (RV64 only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x6502  # C.LDSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD
```

</details>

#### C.LWSP: expands to LW rd, offset(x2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x4502  # C.LWSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD
```

</details>

#### C.SDSP: expands to SD rs2, offset(x2) (RV64 only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0xE50A  # C.SDSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x23)  # STORE
```

</details>

#### C.SWSP: expands to SW rs2, offset(x2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0xC50A  # C.SWSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x23)  # STORE
```

</details>

#### C.JR: expands to JALR x0, 0(rs1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x8502  # C.JR x10
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x67)  # JALR
```

</details>

#### C.MV: expands to ADD rd, x0, rs2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x850A  # C.MV x10, x10 (approx)
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x33)  # OP
```

</details>

#### C.ADD: expands to ADD rd, rd, rs2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressed = 0x950A  # C.ADD x10, x10 (approx)
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x33)  # OP
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
