# Isel Riscv64 Specification

> <details>

<!-- sdn-diagram:id=isel_riscv64_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=isel_riscv64_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

isel_riscv64_spec -> std
isel_riscv64_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=isel_riscv64_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Isel Riscv64 Specification

## Scenarios

### Isel Riscv64

#### uses the shared LP64D contract word size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(RV64_WORD_SIZE).to_equal(8)
expect(contract.pointer_bits).to_equal(64)
expect(contract.stack_align_bytes).to_equal(16)
```

</details>

#### keeps RV64 Linux ABI metadata explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.abi_text()).to_equal("lp64d")
expect(contract.arg_register_count).to_equal(8)
```

</details>

### RV64 native ISel scalar bitmanip

#### selects rotates and unary bitmanip helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rol = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(7), BIT_ROTATE_LEFT, [virt_operand(3), virt_operand(4)])
expect(rol.insts.len()).to_equal(1)
expect(rol.insts[0].opcode).to_equal(RV_OP_ROL)
expect(reg_id(operand_get_reg(rol.insts[0].operands[0]))).to_equal(7)

val ror = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(7), BIT_ROTATE_RIGHT, [virt_operand(3), virt_operand(4)])
expect(ror.insts.len()).to_equal(1)
expect(ror.insts[0].opcode).to_equal(RV_OP_ROR)

val clz = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(5), BIT_CLZ, [virt_operand(2)])
expect(clz.insts[0].opcode).to_equal(RV_OP_CLZ)

val ctz = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(5), BIT_CTZ, [virt_operand(2)])
expect(ctz.insts[0].opcode).to_equal(RV_OP_CTZ)

val bswap = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(5), BIT_BSWAP, [virt_operand(2)])
expect(bswap.insts[0].opcode).to_equal(RV_OP_REV8)
```

</details>

#### keeps unsupported or malformed intrinsics inert

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsupported = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(1), "bit_popcount", [virt_operand(0)])
expect(unsupported.insts.len()).to_equal(1)
expect(unsupported.insts[0].opcode).to_equal(RV_OP_NOP)

val malformed = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(1), BIT_ROTATE_LEFT, [virt_operand(0)])
expect(malformed.insts.len()).to_equal(1)
expect(malformed.insts[0].opcode).to_equal(RV_OP_NOP)
```

</details>

#### lowers rotate intrinsics through the RV64 module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rol_block = entry_block(isel_module_riscv64(build_intrinsic_module("rol_test", BIT_ROTATE_LEFT, 2)))
expect(find_opcode(rol_block, RV_OP_ROL) >= 0).to_equal(true)

val ror_block = entry_block(isel_module_riscv64(build_intrinsic_module("ror_test", BIT_ROTATE_RIGHT, 2)))
expect(find_opcode(ror_block, RV_OP_ROR) >= 0).to_equal(true)
```

</details>

#### lowers clz/ctz/bswap intrinsics through the RV64 module path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clz_block = entry_block(isel_module_riscv64(build_intrinsic_module("clz_test", BIT_CLZ, 1)))
expect(find_opcode(clz_block, RV_OP_CLZ) >= 0).to_equal(true)

val ctz_block = entry_block(isel_module_riscv64(build_intrinsic_module("ctz_test", BIT_CTZ, 1)))
expect(find_opcode(ctz_block, RV_OP_CTZ) >= 0).to_equal(true)

val bswap_block = entry_block(isel_module_riscv64(build_intrinsic_module("bswap_test", BIT_BSWAP, 1)))
expect(find_opcode(bswap_block, RV_OP_REV8) >= 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/isel_riscv64_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Isel Riscv64
- RV64 native ISel scalar bitmanip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
