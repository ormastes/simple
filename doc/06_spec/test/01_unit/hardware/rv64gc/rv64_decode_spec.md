# RV64 Instruction Decode Unit Tests

> Unit tests for instruction field extraction on 64-bit RISC-V. All RV32/RV64 base instructions are 32-bit encoded. Field extraction is shared; this file tests via the RV64 decode module.

<!-- sdn-diagram:id=rv64_decode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_decode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_decode_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_decode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Instruction Decode Unit Tests

Unit tests for instruction field extraction on 64-bit RISC-V. All RV32/RV64 base instructions are 32-bit encoded. Field extraction is shared; this file tests via the RV64 decode module.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-DECODE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_decode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for instruction field extraction on 64-bit RISC-V.
All RV32/RV64 base instructions are 32-bit encoded.
Field extraction is shared; this file tests via the RV64 decode module.

## Scenarios

### Field Extraction

#### extracts opcode from ADDI x10, x0, 10

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00A00513
expect(decode_opcode(instr)).to_equal(OP_OP_IMM)
```

</details>

#### extracts rd correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00A00513  # ADDI x10, x0, 10
expect(decode_rd(instr)).to_equal(10)
```

</details>

#### extracts rs1 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00A00513  # ADDI x10, x0, 10
expect(decode_rs1(instr)).to_equal(0)
```

</details>

#### extracts rs2 from R-type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00B50533  # ADD x10, x10, x11
expect(decode_rs2(instr)).to_equal(11)
```

</details>

#### extracts funct3 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00A00513  # ADDI x10, x0, 10 (funct3=0)
expect(decode_funct3(instr)).to_equal(0)
```

</details>

#### extracts funct7 from R-type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x40B50533  # SUB x10, x10, x11 (funct7=0x20)
expect(decode_funct7(instr)).to_equal(0x20)
```

</details>

### I-Type Immediate

#### positive immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00A00513  # ADDI x10, x0, 10
expect(decode_imm_i(instr)).to_equal(10)
```

</details>

#### negative immediate sign-extends to 64 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0xFFB00513  # ADDI x10, x0, -5
expect(decode_imm_i(instr)).to_equal(-5)
```

</details>

#### zero immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00000513  # ADDI x10, x0, 0
expect(decode_imm_i(instr)).to_equal(0)
```

</details>

#### max positive immediate (2047)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x7FF00513  # ADDI x10, x0, 2047
expect(decode_imm_i(instr)).to_equal(2047)
```

</details>

### S-Type Immediate

#### positive S-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SW x11, 8(x10) => imm=8, rs2=11, rs1=10, funct3=2
val instr = 0x00B52423  # SW x11, 8(x10)
expect(decode_imm_s(instr)).to_equal(8)
```

</details>

#### negative S-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SW x11, -4(x10) => imm=-4
val instr = 0xFEB52E23  # SW x11, -4(x10)
expect(decode_imm_s(instr)).to_equal(-4)
```

</details>

#### zero S-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00B52023  # SW x11, 0(x10)
expect(decode_imm_s(instr)).to_equal(0)
```

</details>

### B-Type Immediate

#### positive B-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BEQ x10, x11, +8
val instr = 0x00B50463  # BEQ x10, x11, 8
expect(decode_imm_b(instr)).to_equal(8)
```

</details>

#### negative B-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BEQ x10, x11, -8
val instr = 0xFEB50CE3  # BEQ x10, x11, -8
expect(decode_imm_b(instr)).to_equal(-8)
```

</details>

#### B-type immediate is always even

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00B50463  # BEQ x10, x11, 8
val imm = decode_imm_b(instr)
expect(imm % 2).to_equal(0)
```

</details>

### U-Type Immediate

#### LUI immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LUI x10, 0x12345
val instr = 0x12345537  # LUI x10, 0x12345
expect(decode_imm_u(instr)).to_equal(0x12345000)
```

</details>

#### LUI with sign bit set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LUI x10, 0x80000
val instr = 0x80000537  # LUI x10, 0x80000
val imm = decode_imm_u(instr)
expect(imm and 0xFFFFF000).to_equal(0xFFFFFFFF80000000)
```

</details>

### J-Type Immediate

#### positive J-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# JAL x1, +8
val instr = 0x008000EF  # JAL x1, 8
expect(decode_imm_j(instr)).to_equal(8)
```

</details>

#### negative J-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# JAL x1, -4
val instr = 0xFFDFF0EF  # JAL x1, -4
expect(decode_imm_j(instr)).to_equal(-4)
```

</details>

#### J-type immediate is always even

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x008000EF  # JAL x1, 8
val imm = decode_imm_j(instr)
expect(imm % 2).to_equal(0)
```

</details>

### RV64 OP-32 Opcode Decode

#### identifies OP_OP_32 opcode (0x3B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ADDW x10, x11, x12 => opcode=0x3B
val instr = 0x00C585BB  # ADDW x11, x11, x12
expect(decode_opcode(instr)).to_equal(OP_OP_32)
```

</details>

#### identifies OP_IMM_32 opcode (0x1B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ADDIW x10, x0, 5 => opcode=0x1B
val instr = 0x0050051B  # ADDIW x10, x0, 5
expect(decode_opcode(instr)).to_equal(OP_OP_IMM_32)
```

</details>

### ALU Operation Mapping

#### ADD: opcode=OP, funct3=0, funct7=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL)
expect(op == AluOp.Add).to_equal(true)
```

</details>

#### SUB: opcode=OP, funct3=0, funct7=0x20

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_alu_op(OP_OP, F3_ADD_SUB, F7_SUB_SRA)
expect(op == AluOp.Sub).to_equal(true)
```

</details>

#### AND: opcode=OP, funct3=7, funct7=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_alu_op(OP_OP, F3_AND, F7_NORMAL)
expect(op == AluOp.And).to_equal(true)
```

</details>

#### OR: opcode=OP, funct3=6, funct7=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_alu_op(OP_OP, F3_OR, F7_NORMAL)
expect(op == AluOp.Or).to_equal(true)
```

</details>

#### XOR: opcode=OP, funct3=4, funct7=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_alu_op(OP_OP, F3_XOR, F7_NORMAL)
expect(op == AluOp.Xor).to_equal(true)
```

</details>

#### SLT: opcode=OP, funct3=2, funct7=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_alu_op(OP_OP, F3_SLT, F7_NORMAL)
expect(op == AluOp.Slt).to_equal(true)
```

</details>

### Branch Operation Mapping

#### BEQ: funct3=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_branch_op(F3_BEQ)
expect(op == BranchOp.Beq).to_equal(true)
```

</details>

#### BNE: funct3=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_branch_op(F3_BNE)
expect(op == BranchOp.Bne).to_equal(true)
```

</details>

#### BLT: funct3=4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_branch_op(F3_BLT)
expect(op == BranchOp.Blt).to_equal(true)
```

</details>

#### BGE: funct3=5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_branch_op(F3_BGE)
expect(op == BranchOp.Bge).to_equal(true)
```

</details>

#### BLTU: funct3=6

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val op = decode_branch_op(F3_BLTU)
expect(op == BranchOp.Bltu).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
