# rv64_ex_stage_spec

> RV64 Execute Stage Unit Specification

<!-- sdn-diagram:id=rv64_ex_stage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_ex_stage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_ex_stage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_ex_stage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_ex_stage_spec

RV64 Execute Stage Unit Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HW-RV64-PIPE-EX |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/hardware/rv64/pipeline/rv64_ex_stage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

RV64 Execute Stage Unit Specification

Tests the 64-bit ALU, branch evaluation, and W-suffix operations.

## Scenarios

### RV64 64-bit ALU (compute_alu)

#### computes ADD

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Add, 10, 32)).to_equal(42)
```

</details>

#### computes SUB

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Sub, 50, 8)).to_equal(42)
```

</details>

#### computes AND

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.And, 0xFF, 0x0F)).to_equal(0x0F)
```

</details>

#### computes OR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Or, 0xF0, 0x0F)).to_equal(0xFF)
```

</details>

#### computes XOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Xor, 0xFF, 0x0F)).to_equal(0xF0)
```

</details>

#### computes SLL (shift left logical)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Sll, 1, 4)).to_equal(16)
```

</details>

#### computes SLT (set less than) true case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Slt, -1, 0)).to_equal(1)
```

</details>

#### computes SLT false case

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Slt, 5, 3)).to_equal(0)
```

</details>

#### computes PassB (forward second operand)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.PassB, 999, 42)).to_equal(42)
```

</details>

#### computes ADDW (32-bit add, sign-extend)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Addw, 1, 2)).to_equal(3)
```

</details>

#### computes ADDW with 32-bit overflow wrapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 0x7FFFFFFF
val b = 1
val result = compute_alu(Rv64AluOp.Addw, a, b)
# 0x80000000 sign-extends to negative 64-bit value
expect(result).to_equal(-2147483648)
```

</details>

#### computes SUBW

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_alu(Rv64AluOp.Subw, 10, 3)).to_equal(7)
```

</details>

### sign_extend_32

#### preserves small positive values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_extend_32(42)).to_equal(42)
```

</details>

#### sign-extends 0x80000000 to negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_extend_32(0x80000000)).to_equal(-2147483648)
```

</details>

#### sign-extends 0xFFFFFFFF to -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_extend_32(0xFFFFFFFF)).to_equal(-1)
```

</details>

### evaluate_branch

#### BEQ taken when equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(evaluate_branch(0, 42, 42)).to_equal(true)
```

</details>

#### BEQ not taken when not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(evaluate_branch(0, 42, 43)).to_equal(false)
```

</details>

#### BNE taken when not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(evaluate_branch(1, 1, 2)).to_equal(true)
```

</details>

#### BNE not taken when equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(evaluate_branch(1, 5, 5)).to_equal(false)
```

</details>

#### BLT taken when rs1 < rs2 signed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(evaluate_branch(4, -1, 0)).to_equal(true)
```

</details>

#### BGE taken when rs1 >= rs2 signed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(evaluate_branch(5, 0, -1)).to_equal(true)
```

</details>

### Rv64ExStage

#### produces invalid latch for invalid input

1. var ex = create rv64 ex stage
   - Expected: latch.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ex = create_rv64_ex_stage()
val latch = ex.tick(create_id_ex_latch())
expect(latch.valid).to_equal(false)
```

</details>

#### computes ADDI result (rs1 + imm)

1. var ex = create rv64 ex stage
2. var id ex = create id ex latch
   - Expected: result.valid is true
   - Expected: result.alu_result equals `142`
   - Expected: result.reg_write is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ex = create_rv64_ex_stage()
var id_ex = create_id_ex_latch()
id_ex = Rv64IdExLatch(
    pc: 0, rs1_val: 100, rs2_val: 0, imm: 42,
    rd: 5, rs1: 1, rs2: 0,
    alu_op: Rv64AluOp.Add, alu_src_b_imm: true,
    mem_read: false, mem_write: false, mem_to_reg: false,
    reg_write: true, branch: false, jump: false,
    inst_type: Rv64InstType.IType, funct3: 0,
    valid: true
)
val result = ex.tick(id_ex)
expect(result.valid).to_equal(true)
expect(result.alu_result).to_equal(142)
expect(result.reg_write).to_equal(true)
```

</details>

#### evaluates BEQ taken and computes branch target

1. var ex = create rv64 ex stage
   - Expected: result.branch_taken is true
   - Expected: result.branch_target equals `0x108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ex = create_rv64_ex_stage()
var id_ex = Rv64IdExLatch(
    pc: 0x100, rs1_val: 5, rs2_val: 5, imm: 8,
    rd: 0, rs1: 1, rs2: 2,
    alu_op: Rv64AluOp.Add, alu_src_b_imm: false,
    mem_read: false, mem_write: false, mem_to_reg: false,
    reg_write: false, branch: true, jump: false,
    inst_type: Rv64InstType.BType, funct3: 0,
    valid: true
)
val result = ex.tick(id_ex)
expect(result.branch_taken).to_equal(true)
expect(result.branch_target).to_equal(0x108)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
