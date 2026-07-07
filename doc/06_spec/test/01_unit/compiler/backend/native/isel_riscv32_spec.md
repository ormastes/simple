# Isel Riscv32 Specification

> <details>

<!-- sdn-diagram:id=isel_riscv32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=isel_riscv32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

isel_riscv32_spec -> std
isel_riscv32_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=isel_riscv32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Isel Riscv32 Specification

## Scenarios

### Isel Riscv32

#### uses the shared ILP32D contract word size

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(RV32_WORD_SIZE).to_equal(4)
expect(contract.pointer_bits / 8).to_equal(4)
expect(contract.pointer_bits).to_equal(32)
expect(contract.stack_align_bytes).to_equal(16)
```

</details>

#### keeps RV32 Linux ABI metadata explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.abi_text()).to_equal("ilp32d")
expect(contract.arg_register_count).to_equal(8)
```

</details>

#### emits RV32 prologue saves for ra and s0

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv32(build_rv32_memory_module())
val block = prologue_block(module)
expect(module.functions[0].frame_size).to_equal(32)
expect(block.insts.len()).to_equal(4)
expect(block.insts[0].opcode).to_equal(RV_OP_ADDI)
expect(operand_reg_id(block.insts[0].operands[0])).to_equal(RV_X2)
expect(operand_reg_id(block.insts[0].operands[1])).to_equal(RV_X2)
expect(operand_imm(block.insts[0].operands[2])).to_equal(-32)
expect(block.insts[1].opcode).to_equal(RV_OP_SW)
expect(operand_reg_id(block.insts[1].operands[0])).to_equal(RV_X1)
expect(mem_offset(block.insts[1].operands[1])).to_equal(28)
expect(block.insts[2].opcode).to_equal(RV_OP_SW)
expect(operand_reg_id(block.insts[2].operands[0])).to_equal(RV_X8)
expect(mem_offset(block.insts[2].operands[1])).to_equal(24)
expect(block.insts[3].opcode).to_equal(RV_OP_ADDI)
expect(operand_reg_id(block.insts[3].operands[0])).to_equal(RV_X8)
expect(operand_reg_id(block.insts[3].operands[1])).to_equal(RV_X2)
expect(operand_imm(block.insts[3].operands[2])).to_equal(32)
```

</details>

#### materializes large RV32 prologue frame offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = prologue_block(isel_module_riscv32(build_rv32_large_alloc_module()))
expect(block.insts[0].opcode).to_equal(RV_OP_LI)
expect(operand_imm(block.insts[0].operands[1])).to_be_less_than(-2047)
expect(block.insts[1].opcode).to_equal(RV_OP_ADD)
expect(operand_reg_id(block.insts[1].operands[0])).to_equal(RV_X2)
expect(block.insts[4].opcode).to_equal(RV_OP_SW)
expect(mem_offset(block.insts[4].operands[1])).to_equal(0)
```

</details>

#### materializes large RV32 epilogue frame offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_large_alloc_return_module()))
expect(has_large_stack_load(block, RV_OP_LW, RV_X1)).to_equal(true)
expect(has_large_stack_load(block, RV_OP_LW, RV_X8)).to_equal(true)
expect(count_opcode(block, RV_OP_RET)).to_equal(1)
```

</details>

#### uses 32-bit load and store opcodes for RV32 memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_memory_module()))
expect(has_opcode(block, RV_OP_LW)).to_equal(true)
expect(has_opcode(block, RV_OP_SW)).to_equal(true)
expect(has_opcode(block, RV_OP_LD)).to_equal(false)
expect(has_opcode(block, RV_OP_SD)).to_equal(false)
expect(nth_dest_reg(block, RV_OP_LW, 0)).to_equal(3)
expect(nth_mem_base_reg(block, RV_OP_LW, 0)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SW, 0, 0)).to_equal(2)
expect(nth_mem_base_reg(block, RV_OP_SW, 0)).to_equal(1)
```

</details>

#### uses RV32 word-size offsets for field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_memory_module()))
expect(nth_mem_offset(block, RV_OP_LW, 1)).to_equal(2 * RV32_WORD_SIZE)
expect(nth_mem_offset(block, RV_OP_SW, 1)).to_equal(3 * RV32_WORD_SIZE)
expect(nth_dest_reg(block, RV_OP_LW, 1)).to_equal(3)
expect(nth_mem_base_reg(block, RV_OP_LW, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SW, 1, 0)).to_equal(2)
expect(nth_mem_base_reg(block, RV_OP_SW, 1)).to_equal(1)
```

</details>

#### materializes RV32 out-of-range field offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_large_field_module()))
expect(has_li_imm(block, 600 * RV32_WORD_SIZE)).to_equal(true)
expect(has_li_imm(block, 601 * RV32_WORD_SIZE)).to_equal(true)
expect(nth_mem_offset(block, RV_OP_LW, 0)).to_equal(0)
expect(nth_mem_base_reg(block, RV_OP_LW, 0)).to_be_greater_than(31)
expect(nth_mem_offset(block, RV_OP_SW, 0)).to_equal(0)
expect(nth_mem_base_reg(block, RV_OP_SW, 0)).to_be_greater_than(31)
```

</details>

#### moves RV32 return values into a0 before RET

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_memory_module()))
expect(last_dest_reg(block, RV_OP_MV)).to_equal(RV_X10)
expect(count_opcode(block, RV_OP_RET)).to_equal(1)
expect(first_operand_count(block, RV_OP_RET)).to_equal(0)
```

</details>

#### emits RV32 epilogue restores for ra and s0

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_memory_module()))
val tail = block.insts.len() - 4
expect(block.insts[tail].opcode).to_equal(RV_OP_LW)
expect(operand_reg_id(block.insts[tail].operands[0])).to_equal(RV_X1)
expect(mem_offset(block.insts[tail].operands[1])).to_equal(28)
expect(block.insts[tail + 1].opcode).to_equal(RV_OP_LW)
expect(operand_reg_id(block.insts[tail + 1].operands[0])).to_equal(RV_X8)
expect(mem_offset(block.insts[tail + 1].operands[1])).to_equal(24)
expect(block.insts[tail + 2].opcode).to_equal(RV_OP_ADDI)
expect(operand_reg_id(block.insts[tail + 2].operands[0])).to_equal(RV_X2)
expect(operand_reg_id(block.insts[tail + 2].operands[1])).to_equal(RV_X2)
expect(operand_imm(block.insts[tail + 2].operands[2])).to_equal(32)
expect(block.insts[tail + 3].opcode).to_equal(RV_OP_RET)
```

</details>

#### selects RV32 address arithmetic for MIR get-element-pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_gep_module()))
expect(count_opcode(block, RV_OP_MUL)).to_equal(1)
expect(count_opcode(block, RV_OP_ADD)).to_equal(1)
expect(first_operand_count(block, RV_OP_MUL)).to_equal(3)
expect(first_operand_count(block, RV_OP_ADD)).to_equal(3)
val scaled_index = nth_dest_reg(block, RV_OP_MUL, 0)
expect(nth_dest_reg(block, RV_OP_ADD, 0)).to_equal(3)
expect(nth_operand_reg(block, RV_OP_ADD, 0, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_ADD, 0, 2)).to_equal(scaled_index)
expect(nth_dest_reg(block, RV_OP_MV, 2)).to_equal(4)
expect(nth_operand_reg(block, RV_OP_MV, 2, 1)).to_equal(1)
expect(has_opcode(block, RV_OP_NOP)).to_equal(false)
```

</details>

#### selects RV32 arithmetic opcodes for MIR binary ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_binop_module()))
expect(has_opcode(block, RV_OP_ADD)).to_equal(true)
expect(has_opcode(block, RV_OP_SUB)).to_equal(true)
expect(has_opcode(block, RV_OP_MUL)).to_equal(true)
expect(nth_dest_reg(block, RV_OP_ADD, 0)).to_equal(3)
expect(nth_operand_reg(block, RV_OP_ADD, 0, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_ADD, 0, 2)).to_equal(2)
expect(nth_dest_reg(block, RV_OP_SUB, 0)).to_equal(4)
expect(nth_operand_reg(block, RV_OP_SUB, 0, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SUB, 0, 2)).to_equal(2)
expect(nth_dest_reg(block, RV_OP_MUL, 0)).to_equal(5)
expect(nth_operand_reg(block, RV_OP_MUL, 0, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_MUL, 0, 2)).to_equal(2)
```

</details>

#### selects RV32 comparison opcodes for MIR binary ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_binop_module()))
expect(has_opcode(block, RV_OP_SLT)).to_equal(true)
expect(has_opcode(block, RV_OP_SEQZ)).to_equal(true)
expect(has_opcode(block, RV_OP_SNEZ)).to_equal(true)
expect(count_opcode(block, RV_OP_SUB)).to_equal(3)
expect(count_opcode(block, RV_OP_SLT)).to_equal(4)
expect(count_opcode(block, RV_OP_SEQZ)).to_equal(3)
expect(nth_operand_reg(block, RV_OP_SUB, 1, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SUB, 1, 2)).to_equal(2)
expect(nth_operand_reg(block, RV_OP_SUB, 2, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SUB, 2, 2)).to_equal(2)
expect(nth_dest_reg(block, RV_OP_SEQZ, 0)).to_equal(6)
expect(nth_operand_reg(block, RV_OP_SEQZ, 0, 1)).to_equal(nth_dest_reg(block, RV_OP_SUB, 1))
expect(nth_dest_reg(block, RV_OP_SNEZ, 0)).to_equal(7)
expect(nth_operand_reg(block, RV_OP_SNEZ, 0, 1)).to_equal(nth_dest_reg(block, RV_OP_SUB, 2))
expect(nth_dest_reg(block, RV_OP_SLT, 0)).to_equal(8)
expect(nth_operand_reg(block, RV_OP_SLT, 0, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SLT, 0, 2)).to_equal(2)
expect(nth_operand_reg(block, RV_OP_SLT, 1, 1)).to_equal(2)
expect(nth_operand_reg(block, RV_OP_SLT, 1, 2)).to_equal(1)
expect(nth_dest_reg(block, RV_OP_SEQZ, 1)).to_equal(9)
expect(nth_operand_reg(block, RV_OP_SEQZ, 1, 1)).to_equal(nth_dest_reg(block, RV_OP_SLT, 1))
expect(nth_dest_reg(block, RV_OP_SLT, 2)).to_equal(10)
expect(nth_operand_reg(block, RV_OP_SLT, 2, 1)).to_equal(2)
expect(nth_operand_reg(block, RV_OP_SLT, 2, 2)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SLT, 3, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SLT, 3, 2)).to_equal(2)
expect(nth_dest_reg(block, RV_OP_SEQZ, 2)).to_equal(11)
expect(nth_operand_reg(block, RV_OP_SEQZ, 2, 1)).to_equal(nth_dest_reg(block, RV_OP_SLT, 3))
```

</details>

#### selects RV32 bitwise, shift, div, and rem opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_binop_module()))
expect(has_opcode(block, RV_OP_DIV)).to_equal(true)
expect(has_opcode(block, RV_OP_REM)).to_equal(true)
expect(has_opcode(block, RV_OP_AND)).to_equal(true)
expect(has_opcode(block, RV_OP_OR)).to_equal(true)
expect(has_opcode(block, RV_OP_XOR)).to_equal(true)
expect(has_opcode(block, RV_OP_SLL)).to_equal(true)
expect(has_opcode(block, RV_OP_SRA)).to_equal(true)
expect(nth_dest_reg(block, RV_OP_DIV, 0)).to_equal(12)
expect(nth_dest_reg(block, RV_OP_REM, 0)).to_equal(13)
expect(nth_dest_reg(block, RV_OP_AND, 0)).to_equal(14)
expect(nth_dest_reg(block, RV_OP_OR, 0)).to_equal(15)
expect(nth_dest_reg(block, RV_OP_XOR, 0)).to_equal(16)
expect(nth_dest_reg(block, RV_OP_SLL, 0)).to_equal(17)
expect(nth_dest_reg(block, RV_OP_SRA, 0)).to_equal(18)
expect(nth_operand_reg(block, RV_OP_SRA, 0, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SRA, 0, 2)).to_equal(2)
```

</details>

#### selects RV32 MV for MIR copy and move instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_copy_move_module()))
expect(count_opcode(block, RV_OP_MV)).to_equal(3)
expect(nth_dest_reg(block, RV_OP_MV, 1)).to_equal(2)
expect(nth_operand_reg(block, RV_OP_MV, 1, 1)).to_equal(1)
expect(nth_dest_reg(block, RV_OP_MV, 2)).to_equal(3)
expect(nth_operand_reg(block, RV_OP_MV, 2, 1)).to_equal(2)
```

</details>

#### materializes RV32 string constants as data references

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv32(build_rv32_string_const_module())
val block = entry_block(module)
expect(module.data_sections.len()).to_equal(1)
expect(has_opcode(block, RV_OP_AUIPC)).to_equal(true)
expect(has_opcode(block, RV_OP_ADDI)).to_equal(true)
expect(has_opcode(block, RV_OP_MV)).to_equal(true)
```

</details>

#### materializes RV32 zero constants as LI zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_zero_const_module()))
expect(nth_imm(block, RV_OP_LI, 0)).to_equal(0)
expect(has_opcode(block, RV_OP_NOP)).to_equal(false)
```

</details>

#### sign-extends RV32 32-bit integer constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_32bit_wrapped_const_module()))
expect(nth_imm(block, RV_OP_LI, 0)).to_equal(-1)
expect(has_opcode(block, RV_OP_NOP)).to_equal(false)
```

</details>

#### selects RV32 JAL for MIR goto terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_goto_module()))
expect(has_opcode(block, RV_OP_JAL)).to_equal(true)
val discard_reg = nth_dest_reg(block, RV_OP_JAL, 0)
val target_label = nth_label_id(block, RV_OP_JAL, 0, 1)
expect(discard_reg).to_equal(RV_X0)
expect(target_label).to_equal(1)
```

</details>

#### selects RV32 branch and jump opcodes for MIR if terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_if_module()))
expect(has_opcode(block, RV_OP_BNE)).to_equal(true)
expect(has_opcode(block, RV_OP_JAL)).to_equal(true)
val zero_cmp = nth_operand_reg(block, RV_OP_BNE, 0, 1)
val else_discard = nth_dest_reg(block, RV_OP_JAL, 0)
val then_label = nth_label_id(block, RV_OP_BNE, 0, 2)
val else_label = nth_label_id(block, RV_OP_JAL, 0, 1)
expect(zero_cmp).to_equal(RV_X0)
expect(else_discard).to_equal(RV_X0)
expect(then_label).to_equal(1)
expect(else_label).to_equal(2)
```

</details>

#### selects RV32 compare and default jump opcodes for MIR switch terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_switch_module()))
expect(has_opcode(block, RV_OP_LI)).to_equal(true)
expect(has_opcode(block, RV_OP_BEQ)).to_equal(true)
expect(has_opcode(block, RV_OP_JAL)).to_equal(true)
val default_discard = nth_dest_reg(block, RV_OP_JAL, 0)
val case_label = nth_label_id(block, RV_OP_BEQ, 0, 2)
val default_label = nth_label_id(block, RV_OP_JAL, 0, 1)
expect(default_discard).to_equal(RV_X0)
expect(case_label).to_equal(1)
expect(default_label).to_equal(2)
```

</details>

#### selects RV32 NOP for MIR unreachable terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_unreachable_module()))
expect(has_opcode(block, RV_OP_NOP)).to_equal(true)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV32 NOP for unsupported terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_abort_module()))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### selects RV32 unary opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_unary_module()))
expect(has_opcode(block, RV_OP_NEG)).to_equal(true)
expect(count_opcode(block, RV_OP_NOT)).to_equal(2)
expect(nth_dest_reg(block, RV_OP_NEG, 0)).to_equal(2)
expect(nth_operand_reg(block, RV_OP_NEG, 0, 1)).to_equal(1)
expect(nth_dest_reg(block, RV_OP_NOT, 0)).to_equal(3)
expect(nth_operand_reg(block, RV_OP_NOT, 0, 1)).to_equal(1)
expect(nth_dest_reg(block, RV_OP_NOT, 1)).to_equal(4)
expect(nth_operand_reg(block, RV_OP_NOT, 1, 1)).to_equal(1)
```

</details>

#### uses RV32 word-size stack slots for call arguments after a7

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv32(build_rv32_call_module())
val block = entry_block(module)
expect(has_opcode(block, RV_OP_CALL)).to_equal(true)
expect(module.extern_symbols).to_contain("callee")
val call_sym = nth_sym_name(block, RV_OP_CALL, 0, 0)
expect(call_sym).to_equal("callee")
val arg0 = nth_dest_reg(block, RV_OP_MV, 10)
val arg1 = nth_dest_reg(block, RV_OP_MV, 11)
val arg2 = nth_dest_reg(block, RV_OP_MV, 12)
val arg3 = nth_dest_reg(block, RV_OP_MV, 13)
val arg4 = nth_dest_reg(block, RV_OP_MV, 14)
val arg5 = nth_dest_reg(block, RV_OP_MV, 15)
val arg6 = nth_dest_reg(block, RV_OP_MV, 16)
val arg7 = nth_dest_reg(block, RV_OP_MV, 17)
expect(arg0).to_equal(RV_X10)
expect(arg1).to_equal(RV_X11)
expect(arg2).to_equal(RV_X12)
expect(arg3).to_equal(RV_X13)
expect(arg4).to_equal(RV_X14)
expect(arg5).to_equal(RV_X15)
expect(arg6).to_equal(RV_X16)
expect(arg7).to_equal(RV_X17)
val stack0 = nth_mem_offset(block, RV_OP_SW, 0)
val stack1 = nth_mem_offset(block, RV_OP_SW, 1)
expect(stack0).to_equal(0)
expect(stack1).to_equal(RV32_WORD_SIZE)
```

</details>

#### materializes RV32 out-of-range stack argument offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv32(build_rv32_many_arg_call_module())
val block = entry_block(module)
expect(has_li_imm(block, 2048)).to_equal(true)
expect(nth_mem_offset(block, RV_OP_SW, 512)).to_equal(0)
expect(nth_mem_base_reg(block, RV_OP_SW, 512)).to_be_greater_than(31)
```

</details>

#### does not move a return register for RV32 void calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv32(build_rv32_void_call_module())
val block = entry_block(module)
expect(has_opcode(block, RV_OP_CALL)).to_equal(true)
expect(module.extern_symbols).to_contain("void_callee")
val call_sym = nth_sym_name(block, RV_OP_CALL, 0, 0)
expect(call_sym).to_equal("void_callee")
expect(count_opcode_after_first(block, RV_OP_CALL, RV_OP_MV)).to_equal(0)
```

</details>

#### fails closed with RV32 NOP for unsupported call targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_unsupported_call_target_module()))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
expect(has_opcode(block, RV_OP_CALL)).to_equal(false)
expect(has_opcode(block, RV_OP_JALR)).to_equal(false)
expect(count_opcode_after_first(block, RV_OP_NOP, RV_OP_MV)).to_equal(0)
```

</details>

#### selects RV32 JALR for MIR indirect calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_indirect_call_module()))
expect(count_opcode(block, RV_OP_JALR)).to_equal(2)
expect(has_opcode(block, RV_OP_CALL)).to_equal(false)
val first_link = nth_dest_reg(block, RV_OP_JALR, 0)
val second_link = nth_dest_reg(block, RV_OP_JALR, 1)
val first_offset = nth_operand_imm(block, RV_OP_JALR, 0, 2)
val second_offset = nth_operand_imm(block, RV_OP_JALR, 1, 2)
expect(first_link).to_equal(RV_X1)
expect(second_link).to_equal(RV_X1)
expect(first_offset).to_equal(0)
expect(second_offset).to_equal(0)
```

</details>

#### selects RV32 JALR for MIR CallIndirect instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_call_indirect_module()))
expect(count_opcode(block, RV_OP_JALR)).to_equal(1)
expect(has_opcode(block, RV_OP_CALL)).to_equal(false)
val link = nth_dest_reg(block, RV_OP_JALR, 0)
val offset = nth_operand_imm(block, RV_OP_JALR, 0, 2)
expect(link).to_equal(RV_X1)
expect(offset).to_equal(0)
```

</details>

#### selects RV32 stack allocation and cast opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_alloc_cast_module()))
expect(has_opcode(block, RV_OP_ADDI)).to_equal(true)
expect(count_opcode(block, RV_OP_MV)).to_be_greater_than(1)
val alloc_dest = nth_dest_reg(block, RV_OP_ADDI, 0)
val alloc_base = nth_operand_reg(block, RV_OP_ADDI, 0, 1)
val alloc_size = nth_operand_imm(block, RV_OP_ADDI, 0, 2)
val alloc_ptr_dest = nth_dest_reg(block, RV_OP_MV, 0)
val alloc_ptr_base = nth_operand_reg(block, RV_OP_MV, 0, 1)
val cast_dest = nth_dest_reg(block, RV_OP_MV, 2)
val cast_source = nth_operand_reg(block, RV_OP_MV, 2, 1)
expect(alloc_dest).to_equal(RV_X2)
expect(alloc_base).to_equal(RV_X2)
expect(alloc_size).to_equal(-16)
expect(alloc_ptr_dest).to_equal(1)
expect(alloc_ptr_base).to_equal(RV_X2)
expect(cast_dest).to_equal(3)
expect(cast_source).to_equal(2)
```

</details>

#### materializes RV32 large stack allocation sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_large_alloc_module()))
expect(has_li_imm(block, -2400)).to_equal(true)
expect(nth_dest_reg(block, RV_OP_ADD, 0)).to_equal(RV_X2)
expect(nth_operand_reg(block, RV_OP_ADD, 0, 1)).to_equal(RV_X2)
```

</details>

#### selects RV32 NOP for MIR nop instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_nop_inst_module()))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV32 NOP for unsupported MIR instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_unsupported_inst_module()))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV32 NOP for unsupported arithmetic ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_unsupported_ops_module()))
expect(count_opcode(block, RV_OP_NOP)).to_equal(2)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV32 NOP for unsupported MIR constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_unsupported_const_module()))
expect(nth_imm(block, RV_OP_LI, 0)).to_equal(1)
expect(nth_imm(block, RV_OP_LI, 1)).to_equal(0)
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
expect(count_opcode(block, RV_OP_MV)).to_equal(3)
```

</details>

#### fails closed with RV32 NOP for unsupported MIR intrinsics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv32(build_rv32_unsupported_intrinsic_module()))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/isel_riscv32_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Isel Riscv32

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
