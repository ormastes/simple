# Isel Aarch64 Specification

> <details>

<!-- sdn-diagram:id=isel_aarch64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=isel_aarch64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

isel_aarch64_spec -> std
isel_aarch64_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=isel_aarch64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Isel Aarch64 Specification

## Scenarios

### AArch64 native ISel bitmanip intrinsics

#### lowers bit_clz to a single CLZ

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = a64_select_scalar_bitmanip(new_isel_context(), virt_operand(7), "bit_clz", virt_operand(3))
expect(result.insts.len()).to_equal(1)
expect(result.insts[0].opcode).to_equal(A64_OP_CLZ)
expect(reg_id(operand_get_reg(result.insts[0].operands[0]))).to_equal(7)
expect(reg_id(operand_get_reg(result.insts[0].operands[1]))).to_equal(3)
```

</details>

#### lowers bit_ctz to RBIT followed by CLZ

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = a64_select_scalar_bitmanip(new_isel_context(), virt_operand(9), "bit_ctz", virt_operand(4))
expect(result.insts.len()).to_equal(2)
expect(result.insts[0].opcode).to_equal(A64_OP_RBIT)
expect(result.insts[1].opcode).to_equal(A64_OP_CLZ)
val tmp_reg = operand_get_reg(result.insts[0].operands[0])
expect(reg_id(operand_get_reg(result.insts[0].operands[1]))).to_equal(4)
expect(reg_id(operand_get_reg(result.insts[1].operands[0]))).to_equal(9)
expect(reg_id(operand_get_reg(result.insts[1].operands[1]))).to_equal(reg_id(tmp_reg))
```

</details>

#### lowers bit_bswap to REV

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = a64_select_scalar_bitmanip(new_isel_context(), virt_operand(5), "bit_bswap", virt_operand(2))
expect(result.insts.len()).to_equal(1)
expect(result.insts[0].opcode).to_equal(A64_OP_REV)
```

</details>

#### lowers bit_bitreverse to RBIT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = a64_select_scalar_bitmanip(new_isel_context(), virt_operand(6), "bit_bitreverse", virt_operand(1))
expect(result.insts.len()).to_equal(1)
expect(result.insts[0].opcode).to_equal(A64_OP_RBIT)
```

</details>

#### lowers bit_popcount to a scalar SWAR sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = a64_select_scalar_bitmanip(new_isel_context(), virt_operand(1), "bit_popcount", virt_operand(0))
expect(result.ctx.next_vreg).to_equal(3)
expect(result.insts.len()).to_equal(37)
expect(result.insts[0].opcode).to_equal(A64_OP_MOV)
expect(result.insts[1].opcode).to_equal(A64_OP_MOVZ)
expect(result.insts[2].opcode).to_equal(A64_OP_LSR)
expect(result.insts[7].opcode).to_equal(A64_OP_AND)
expect(result.insts[8].opcode).to_equal(A64_OP_SUB)
expect(result.insts[13].opcode).to_equal(A64_OP_MOVK)
expect(result.insts[16].opcode).to_equal(A64_OP_AND)
expect(result.insts[17].opcode).to_equal(A64_OP_ADD)
expect(result.insts[35].opcode).to_equal(A64_OP_MOVZ)
expect(result.insts[36].opcode).to_equal(A64_OP_AND)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/isel_aarch64_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AArch64 native ISel bitmanip intrinsics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
