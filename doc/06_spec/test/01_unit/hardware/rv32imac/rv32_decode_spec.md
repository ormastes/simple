# RV32 Decode Unit Tests

> Unit tests for instruction field extraction and immediate decoding.

<!-- sdn-diagram:id=rv32_decode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_decode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_decode_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_decode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 Decode Unit Tests

Unit tests for instruction field extraction and immediate decoding.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-DECODE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/hardware/rv32imac/rv32_decode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for instruction field extraction and immediate decoding.

## Scenarios

### Instruction Field Extraction

#### extracts all fields from ADD x1, x2, x3

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x003100B3
expect(decode_opcode(instr)).to_equal(0x33)
expect(decode_rd(instr)).to_equal(1)
expect(decode_rs1(instr)).to_equal(2)
expect(decode_rs2(instr)).to_equal(3)
expect(decode_funct3(instr)).to_equal(0)
expect(decode_funct7(instr)).to_equal(0)
```

</details>

#### extracts fields from SUB x5, x6, x7

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x407302B3
expect(decode_opcode(instr)).to_equal(0x33)
expect(decode_rd(instr)).to_equal(5)
expect(decode_funct7(instr)).to_equal(0x20)
```

</details>

### Immediate Decoding

#### decodes positive I-type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = decode_imm_i(0x06400093)  # ADDI x1, x0, 100
expect(imm).to_equal(100)
```

</details>

#### decodes negative I-type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = decode_imm_i(0xFFF00093)  # ADDI x1, x0, -1
expect(imm and 0xFFFFFFFF).to_equal(0xFFFFFFFF)
```

</details>

#### decodes U-type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = decode_imm_u(0x123450B7)  # LUI x1, 0x12345
expect(imm).to_equal(0x12345000)
```

</details>

### ALU Operation Decode

#### maps ADD correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_alu_op(OP_OP, 0, 0) == AluOp.Add).to_equal(true)
```

</details>

#### maps SUB correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_alu_op(OP_OP, 0, 0x20) == AluOp.Sub).to_equal(true)
```

</details>

#### maps MUL correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_alu_op(OP_OP, 0, 0x01) == AluOp.Mul).to_equal(true)
```

</details>

#### maps AND correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_alu_op(OP_OP, 7, 0) == AluOp.And).to_equal(true)
```

</details>

### Branch Operation Decode

#### maps BEQ correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_branch_op(OP_BRANCH, F3_BEQ) == BranchOp.Beq).to_equal(true)
```

</details>

#### maps BNE correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_branch_op(OP_BRANCH, F3_BNE) == BranchOp.Bne).to_equal(true)
```

</details>

#### maps JAL correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_branch_op(OP_JAL, 0) == BranchOp.Jal).to_equal(true)
```

</details>

#### maps JALR correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_branch_op(OP_JALR, 0) == BranchOp.Jalr).to_equal(true)
```

</details>

#### returns None for non-branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(decode_branch_op(OP_OP, 0) == BranchOp.None).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
