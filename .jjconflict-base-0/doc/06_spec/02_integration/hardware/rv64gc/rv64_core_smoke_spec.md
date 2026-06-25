# RV64 Core Smoke Integration Tests

> Quick validation that basic instruction execution works end-to-end. Tests compose multiple modules (decode + execute + regfile + memory).

<!-- sdn-diagram:id=rv64_core_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_core_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_core_smoke_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_core_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Core Smoke Integration Tests

Quick validation that basic instruction execution works end-to-end. Tests compose multiple modules (decode + execute + regfile + memory).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-SMOKE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/02_integration/hardware/rv64gc/rv64_core_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Quick validation that basic instruction execution works end-to-end.
Tests compose multiple modules (decode + execute + regfile + memory).

## Scenarios

### Register File + ALU Integration

#### ADD two registers

1. var rf = Rv64RegFile create
2. rf write
3. rf write
4. rf write
   - Expected: rf.read(12) equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(10, 100)
rf.write(11, 200)
val result = alu_execute(AluOp.Add, rf.read(10), rf.read(11))
rf.write(12, result)
expect(rf.read(12)).to_equal(300)
```

</details>

#### SUB with register values

1. var rf = Rv64RegFile create
2. rf write
3. rf write
4. rf write
   - Expected: rf.read(12) equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(10, 500)
rf.write(11, 200)
val result = alu_execute(AluOp.Sub, rf.read(10), rf.read(11))
rf.write(12, result)
expect(rf.read(12)).to_equal(300)
```

</details>

#### AND with mask

1. var rf = Rv64RegFile create
2. rf write
3. rf write
4. rf write
   - Expected: rf.read(12) equals `0x0F000F000F000F00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(10, 0xFF00FF00FF00FF00)
rf.write(11, 0x0F0F0F0F0F0F0F0F)
val result = alu_execute(AluOp.And, rf.read(10), rf.read(11))
rf.write(12, result)
expect(rf.read(12)).to_equal(0x0F000F000F000F00)
```

</details>

### 64-bit ALU Edge Cases

#### SLL by 32 moves to upper half

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute(AluOp.Sll, 0xDEADBEEF, 32)
expect(result).to_equal(0xDEADBEEF00000000)
```

</details>

#### SRL by 32 moves from upper half

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute(AluOp.Srl, 0xDEADBEEF00000000, 32)
expect(result).to_equal(0xDEADBEEF)
```

</details>

#### SRA preserves negative sign through 64 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute(AluOp.Sra, 0x8000000000000000, 32)
expect(result).to_equal(0xFFFFFFFF80000000)
```

</details>

#### SLTU: large unsigned comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = alu_execute(AluOp.Sltu, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000)
expect(result).to_equal(1)
```

</details>

### W-Variant Integration

#### ADDW result stored in register

1. var rf = Rv64RegFile create
2. rf write
3. rf write
   - Expected: rf.read(11) equals `0xFFFFFFFF80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(10, 0x7FFFFFFF)
val result = alu_execute_word(AluOp.Addw, rf.read(10), 1)
rf.write(11, result)
expect(rf.read(11)).to_equal(0xFFFFFFFF80000000)
```

</details>

#### SUBW with register values

1. var rf = Rv64RegFile create
2. rf write
3. rf write
4. rf write
   - Expected: rf.read(12) equals `0xFFFFFFFFFFFFFFEC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = Rv64RegFile.create()
rf.write(10, 10)
rf.write(11, 30)
val result = alu_execute_word(AluOp.Subw, rf.read(10), rf.read(11))
rf.write(12, result)
expect(rf.read(12)).to_equal(0xFFFFFFFFFFFFFFEC)
```

</details>

### Decode + Execute Pipeline

#### decode ADDI and execute

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00A00513  # ADDI x10, x0, 10
val opcode = decode_opcode(instr)
val rd = decode_rd(instr)
val rs1 = decode_rs1(instr)
val imm = decode_imm_i(instr)
expect(opcode).to_equal(OP_OP_IMM)
expect(rd).to_equal(10)
val result = alu_execute(AluOp.Add, 0, imm)
expect(result).to_equal(10)
```

</details>

#### decode LUI and compute

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x12345537  # LUI x10, 0x12345
val rd = decode_rd(instr)
val imm = decode_imm_u(instr)
expect(rd).to_equal(10)
expect(imm).to_equal(0x12345000)
```

</details>

#### decode R-type ADD

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instr = 0x00B50533  # ADD x10, x10, x11
val opcode = decode_opcode(instr)
val funct3 = decode_funct3(instr)
val funct7 = decode_funct7(instr)
val alu_op = decode_alu_op(opcode, funct3, funct7)
expect(alu_op == AluOp.Add).to_equal(true)
```

</details>

### Branch Resolution

#### BEQ: equal values branch taken

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val taken = (10 == 10)
expect(taken).to_equal(true)
```

</details>

#### BNE: unequal values branch taken

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val taken = (10 != 20)
expect(taken).to_equal(true)
```

</details>

#### BLT: signed less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val taken = (-1 < 0)
expect(taken).to_equal(true)
```

</details>

#### BGE: signed greater or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val taken = (0 >= -1)
expect(taken).to_equal(true)
```

</details>

#### branch target calculation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pc: i64 = 0x80001000
val offset: i64 = 8
expect(pc + offset).to_equal(0x80001008)
```

</details>

### Immediate Decode Consistency

#### sign extension consistent across formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val neg_i = decode_imm_i(0xFFF00513)  # ADDI x10, x0, -1
expect(neg_i).to_equal(-1)
```

</details>

#### U-type upper bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = decode_imm_u(0xFFFFF537)  # LUI x10, 0xFFFFF
expect(imm and 0xFFFFF000).to_equal(0xFFFFFFFFFFFFF000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
