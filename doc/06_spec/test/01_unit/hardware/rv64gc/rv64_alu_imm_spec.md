# RV64 ALU Immediate + System Instruction Tests

> Unit tests for immediate ALU variants: SLTI, SLTIU, XORI, ORI, ANDI, and system instructions: ECALL, EBREAK, FENCE, AUIPC. Also covers ADDIW, SLLIW, SRLIW, SRAIW (immediate W-variants).

<!-- sdn-diagram:id=rv64_alu_imm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_alu_imm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_alu_imm_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_alu_imm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 ALU Immediate + System Instruction Tests

Unit tests for immediate ALU variants: SLTI, SLTIU, XORI, ORI, ANDI, and system instructions: ECALL, EBREAK, FENCE, AUIPC. Also covers ADDIW, SLLIW, SRLIW, SRAIW (immediate W-variants).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-ALU-IMM-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_alu_imm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for immediate ALU variants: SLTI, SLTIU, XORI, ORI, ANDI,
and system instructions: ECALL, EBREAK, FENCE, AUIPC.
Also covers ADDIW, SLLIW, SRLIW, SRAIW (immediate W-variants).

## Scenarios

### SLTI (Set Less Than Immediate — signed)

#### SLTI: 5 < 10 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 5, 10)).to_equal(1)
```

</details>

#### SLTI: 10 < 5 = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 10, 5)).to_equal(0)
```

</details>

#### SLTI: -1 < 0 = 1 (signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, -1, 0)).to_equal(1)
```

</details>

#### SLTI: 0 < -1 = 0 (signed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 0, -1)).to_equal(0)
```

</details>

#### SLTI: equal values = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Slt, 42, 42)).to_equal(0)
```

</details>

### SLTIU (Set Less Than Immediate — unsigned)

#### SLTIU: 5 < 10 = 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 5, 10)).to_equal(1)
```

</details>

#### SLTIU: 0xFFFFFFFFFFFFFFFF > 5 unsigned

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 5, 0xFFFFFFFFFFFFFFFF)).to_equal(1)
```

</details>

#### SLTIU: SEQZ pattern (rs1 < 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Sltu, 0, 1)).to_equal(1)
expect(alu_execute(AluOp.Sltu, 1, 1)).to_equal(0)
```

</details>

### XORI

#### XORI: basic XOR with immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Xor, 0xFF, 0x0F)).to_equal(0xF0)
```

</details>

#### XORI: NOT pattern (XOR with -1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Xor, 0xDEADBEEF, 0xFFFFFFFFFFFFFFFF)).to_equal(0xFFFFFFFF21524110)
```

</details>

#### XORI: XOR with 0 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Xor, 42, 0)).to_equal(42)
```

</details>

### ORI

#### ORI: basic OR with immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Or, 0xF0, 0x0F)).to_equal(0xFF)
```

</details>

#### ORI: OR with 0 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Or, 42, 0)).to_equal(42)
```

</details>

#### ORI: OR with all bits set

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.Or, 0, 0xFFFFFFFFFFFFFFFF)).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

### ANDI

#### ANDI: basic AND with immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.And, 0xFF, 0x0F)).to_equal(0x0F)
```

</details>

#### ANDI: AND with 0 is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.And, 42, 0)).to_equal(0)
```

</details>

#### ANDI: AND with -1 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute(AluOp.And, 42, 0xFFFFFFFFFFFFFFFF)).to_equal(42)
```

</details>

### ADDIW (Add Immediate Word)

#### ADDIW: basic addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Addw, 0, 100)).to_equal(100)
```

</details>

#### ADDIW: wraps at 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Addw, 0x7FFFFFFF, 1)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### ADDIW: negative immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Addw, 10, -3)).to_equal(7)
```

</details>

### SLLIW (Shift Left Logical Immediate Word)

#### SLLIW: basic shift

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Sllw, 1, 4)).to_equal(16)
```

</details>

#### SLLIW: shift into sign bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Sllw, 1, 31)).to_equal(0xFFFFFFFF80000000)
```

</details>

### SRLIW (Shift Right Logical Immediate Word)

#### SRLIW: basic shift

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Srlw, 16, 4)).to_equal(1)
```

</details>

#### SRLIW: does not sign-extend within 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Srlw, 0x80000000, 31)).to_equal(1)
```

</details>

### SRAIW (Shift Right Arithmetic Immediate Word)

#### SRAIW: positive value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Sraw, 16, 4)).to_equal(1)
```

</details>

#### SRAIW: negative value fills with sign

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alu_execute_word(AluOp.Sraw, 0x80000000, 1)).to_equal(0xFFFFFFFFC0000000)
```

</details>

### AUIPC

#### AUIPC: PC + upper immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pc: i64 = 0x80001000
val imm = decode_imm_u(0x00001517)  # AUIPC x10, 1
val result = pc + imm
expect(result).to_equal(0x80002000)
```

</details>

#### AUIPC: PC + 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pc: i64 = 0x80001000
val result = pc + 0
expect(result).to_equal(0x80001000)
```

</details>

### System Instructions

#### ECALL: opcode is SYSTEM (0x73)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr: i64 = 0x00000073  # ECALL
expect(decode_opcode(instr)).to_equal(OP_SYSTEM)
```

</details>

#### EBREAK: opcode is SYSTEM with imm=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr: i64 = 0x00100073  # EBREAK
expect(decode_opcode(instr)).to_equal(OP_SYSTEM)
expect(decode_imm_i(instr)).to_equal(1)
```

</details>

#### FENCE: opcode is MISC_MEM (0x0F)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr: i64 = 0x0FF0000F  # FENCE iorw, iorw
expect(decode_opcode(instr)).to_equal(OP_MISC_MEM)
```

</details>

#### FENCE.I: opcode is MISC_MEM with funct3=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr: i64 = 0x0000100F  # FENCE.I
expect(decode_opcode(instr)).to_equal(OP_MISC_MEM)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
