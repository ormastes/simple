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
| 42 | 42 | 0 | 0 |

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

#### emits RV64 prologue saves for ra and s0

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv64(build_memory_module("rv64_prologue"))
val block = prologue_block(module)
expect(module.functions[0].frame_size).to_equal(48)
expect(block.insts.len()).to_equal(4)
expect(block.insts[0].opcode).to_equal(RV_OP_ADDI)
expect(operand_reg_id(block.insts[0].operands[0])).to_equal(RV_X2)
expect(operand_reg_id(block.insts[0].operands[1])).to_equal(RV_X2)
expect(operand_imm(block.insts[0].operands[2])).to_equal(-48)
expect(block.insts[1].opcode).to_equal(RV_OP_SD)
expect(operand_reg_id(block.insts[1].operands[0])).to_equal(RV_X1)
expect(mem_offset(block.insts[1].operands[1])).to_equal(40)
expect(block.insts[2].opcode).to_equal(RV_OP_SD)
expect(operand_reg_id(block.insts[2].operands[0])).to_equal(RV_X8)
expect(mem_offset(block.insts[2].operands[1])).to_equal(32)
expect(block.insts[3].opcode).to_equal(RV_OP_ADDI)
expect(operand_reg_id(block.insts[3].operands[0])).to_equal(RV_X8)
expect(operand_reg_id(block.insts[3].operands[1])).to_equal(RV_X2)
expect(operand_imm(block.insts[3].operands[2])).to_equal(48)
```

</details>

#### materializes large RV64 prologue frame offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = prologue_block(isel_module_riscv64(build_large_alloc_module("rv64_large_frame")))
expect(block.insts[0].opcode).to_equal(RV_OP_LI)
expect(operand_imm(block.insts[0].operands[1])).to_be_less_than(-2047)
expect(block.insts[1].opcode).to_equal(RV_OP_ADD)
expect(operand_reg_id(block.insts[1].operands[0])).to_equal(RV_X2)
expect(block.insts[4].opcode).to_equal(RV_OP_SD)
expect(mem_offset(block.insts[4].operands[1])).to_equal(0)
```

</details>

#### materializes large RV64 epilogue frame offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_large_alloc_return_module("rv64_large_frame_epilogue")))
expect(has_large_stack_load(block, RV_OP_LD, RV_X1)).to_equal(true)
expect(has_large_stack_load(block, RV_OP_LD, RV_X8)).to_equal(true)
expect(count_opcode(block, RV_OP_RET)).to_equal(1)
```

</details>

#### uses 64-bit load and store opcodes for RV64 memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_memory_module("rv64_memory")))
expect(has_opcode(block, RV_OP_LD)).to_equal(true)
expect(has_opcode(block, RV_OP_SD)).to_equal(true)
expect(has_opcode(block, RV_OP_LW)).to_equal(false)
expect(has_opcode(block, RV_OP_SW)).to_equal(false)
expect(nth_dest_reg(block, RV_OP_LD, 0)).to_equal(3)
expect(nth_mem_base_reg(block, RV_OP_LD, 0)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SD, 0, 0)).to_equal(2)
expect(nth_mem_base_reg(block, RV_OP_SD, 0)).to_equal(1)
```

</details>

#### uses RV64 word-size offsets for field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_memory_module("rv64_fields")))
expect(nth_mem_offset(block, RV_OP_LD, 1)).to_equal(2 * RV64_WORD_SIZE)
expect(nth_mem_offset(block, RV_OP_SD, 1)).to_equal(3 * RV64_WORD_SIZE)
expect(nth_dest_reg(block, RV_OP_LD, 1)).to_equal(3)
expect(nth_mem_base_reg(block, RV_OP_LD, 1)).to_equal(1)
expect(nth_operand_reg(block, RV_OP_SD, 1, 0)).to_equal(2)
expect(nth_mem_base_reg(block, RV_OP_SD, 1)).to_equal(1)
```

</details>

#### materializes RV64 out-of-range field offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_large_field_module("rv64_large_field")))
expect(has_li_imm(block, 300 * RV64_WORD_SIZE)).to_equal(true)
expect(has_li_imm(block, 301 * RV64_WORD_SIZE)).to_equal(true)
expect(nth_mem_offset(block, RV_OP_LD, 0)).to_equal(0)
expect(nth_mem_base_reg(block, RV_OP_LD, 0)).to_be_greater_than(31)
expect(nth_mem_offset(block, RV_OP_SD, 0)).to_equal(0)
expect(nth_mem_base_reg(block, RV_OP_SD, 0)).to_be_greater_than(31)
```

</details>

#### moves RV64 return values into a0 before RET

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_memory_module("rv64_return_value")))
expect(last_dest_reg(block, RV_OP_MV)).to_equal(RV_X10)
expect(count_opcode(block, RV_OP_RET)).to_equal(1)
expect(first_operand_count(block, RV_OP_RET)).to_equal(0)
```

</details>

#### emits RV64 epilogue restores for ra and s0

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_memory_module("rv64_epilogue")))
val tail = block.insts.len() - 4
expect(block.insts[tail].opcode).to_equal(RV_OP_LD)
expect(operand_reg_id(block.insts[tail].operands[0])).to_equal(RV_X1)
expect(mem_offset(block.insts[tail].operands[1])).to_equal(40)
expect(block.insts[tail + 1].opcode).to_equal(RV_OP_LD)
expect(operand_reg_id(block.insts[tail + 1].operands[0])).to_equal(RV_X8)
expect(mem_offset(block.insts[tail + 1].operands[1])).to_equal(32)
expect(block.insts[tail + 2].opcode).to_equal(RV_OP_ADDI)
expect(operand_reg_id(block.insts[tail + 2].operands[0])).to_equal(RV_X2)
expect(operand_reg_id(block.insts[tail + 2].operands[1])).to_equal(RV_X2)
expect(operand_imm(block.insts[tail + 2].operands[2])).to_equal(48)
expect(block.insts[tail + 3].opcode).to_equal(RV_OP_RET)
```

</details>

#### selects RV64 arithmetic opcodes for MIR binary ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_binop_module("rv64_binop")))
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

#### selects RV64 comparison opcodes for MIR binary ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_binop_module("rv64_binop")))
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

#### selects RV64 bitwise, shift, div, and rem opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_binop_module("rv64_binop")))
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

#### selects RV64 MV for MIR copy and move instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_copy_move_module("rv64_copy_move")))
expect(count_opcode(block, RV_OP_MV)).to_equal(3)
expect(nth_dest_reg(block, RV_OP_MV, 1)).to_equal(2)
expect(nth_operand_reg(block, RV_OP_MV, 1, 1)).to_equal(1)
expect(nth_dest_reg(block, RV_OP_MV, 2)).to_equal(3)
expect(nth_operand_reg(block, RV_OP_MV, 2, 1)).to_equal(2)
```

</details>

#### materializes RV64 string constants as data references

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv64(build_string_const_module("rv64_string_const"))
val block = entry_block(module)
expect(module.data_sections.len()).to_equal(1)
expect(has_opcode(block, RV_OP_AUIPC)).to_equal(true)
expect(has_opcode(block, RV_OP_ADDI)).to_equal(true)
expect(has_opcode(block, RV_OP_MV)).to_equal(true)
```

</details>

#### materializes RV64 zero constants as LI zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_zero_const_module("rv64_zero_const")))
expect(nth_imm(block, RV_OP_LI, 0)).to_equal(0)
expect(has_opcode(block, RV_OP_NOP)).to_equal(false)
```

</details>

#### preserves RV64 large integer constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_large_int_const_module("rv64_large_int_const")))
expect(nth_imm(block, RV_OP_LI, 0)).to_equal(4294967295)
expect(has_opcode(block, RV_OP_NOP)).to_equal(false)
```

</details>

#### selects RV64 JAL for MIR goto terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_goto_module("rv64_goto")))
expect(has_opcode(block, RV_OP_JAL)).to_equal(true)
val discard_reg = nth_dest_reg(block, RV_OP_JAL, 0)
val target_label = nth_label_id(block, RV_OP_JAL, 0, 1)
expect(discard_reg).to_equal(RV_X0)
expect(target_label).to_equal(1)
```

</details>

#### selects RV64 branch and jump opcodes for MIR if terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_if_module("rv64_if")))
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

#### selects RV64 compare and default jump opcodes for MIR switch terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_switch_module("rv64_switch")))
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

#### selects RV64 NOP for MIR unreachable terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_unreachable_module("rv64_unreachable")))
expect(has_opcode(block, RV_OP_NOP)).to_equal(true)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV64 NOP for unsupported terminators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_abort_module("rv64_abort")))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### selects RV64 unary opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_unary_module("rv64_unary")))
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

#### uses RV64 word-size stack slots for call arguments after a7

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv64(build_call_module("rv64_call"))
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
val stack0 = nth_mem_offset(block, RV_OP_SD, 0)
val stack1 = nth_mem_offset(block, RV_OP_SD, 1)
expect(stack0).to_equal(0)
expect(stack1).to_equal(RV64_WORD_SIZE)
```

</details>

#### materializes RV64 out-of-range stack argument offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv64(build_many_arg_call_module("rv64_many_arg_call"))
val block = entry_block(module)
expect(has_li_imm(block, 2048)).to_equal(true)
expect(nth_mem_offset(block, RV_OP_SD, 256)).to_equal(0)
expect(nth_mem_base_reg(block, RV_OP_SD, 256)).to_be_greater_than(31)
```

</details>

#### does not move a return register for RV64 void calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = isel_module_riscv64(build_void_call_module("rv64_void_call"))
val block = entry_block(module)
expect(has_opcode(block, RV_OP_CALL)).to_equal(true)
expect(module.extern_symbols).to_contain("void_callee")
val call_sym = nth_sym_name(block, RV_OP_CALL, 0, 0)
expect(call_sym).to_equal("void_callee")
expect(count_opcode_after_first(block, RV_OP_CALL, RV_OP_MV)).to_equal(0)
```

</details>

#### fails closed with RV64 NOP for unsupported call targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_unsupported_call_target_module("rv64_unsupported_call_target")))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
expect(has_opcode(block, RV_OP_CALL)).to_equal(false)
expect(has_opcode(block, RV_OP_JALR)).to_equal(false)
expect(count_opcode_after_first(block, RV_OP_NOP, RV_OP_MV)).to_equal(0)
```

</details>

#### selects RV64 JALR for MIR indirect calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_indirect_call_module("rv64_indirect_call")))
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

#### selects RV64 JALR for MIR CallIndirect instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_call_indirect_module("rv64_call_indirect")))
expect(count_opcode(block, RV_OP_JALR)).to_equal(1)
expect(has_opcode(block, RV_OP_CALL)).to_equal(false)
val link = nth_dest_reg(block, RV_OP_JALR, 0)
val offset = nth_operand_imm(block, RV_OP_JALR, 0, 2)
expect(link).to_equal(RV_X1)
expect(offset).to_equal(0)
```

</details>

#### selects RV64 stack allocation and cast opcodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_alloc_cast_module("rv64_alloc_cast")))
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

#### materializes RV64 large stack allocation sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_large_alloc_module("rv64_large_alloc")))
expect(has_li_imm(block, -2400)).to_equal(true)
expect(nth_dest_reg(block, RV_OP_ADD, 0)).to_equal(RV_X2)
expect(nth_operand_reg(block, RV_OP_ADD, 0, 1)).to_equal(RV_X2)
```

</details>

#### selects RV64 NOP for MIR nop instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_nop_inst_module("rv64_nop_inst")))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV64 NOP for unsupported MIR instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_unsupported_inst_module("rv64_unsupported_inst")))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV64 NOP for unsupported arithmetic ops

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_unsupported_ops_module("rv64_unsupported_ops")))
expect(count_opcode(block, RV_OP_NOP)).to_equal(2)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

#### fails closed with RV64 NOP for unsupported MIR constants

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_unsupported_const_module("rv64_unsupported_const")))
expect(nth_imm(block, RV_OP_LI, 0)).to_equal(1)
expect(nth_imm(block, RV_OP_LI, 1)).to_equal(0)
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
expect(count_opcode(block, RV_OP_MV)).to_equal(3)
```

</details>

### RV64 native ISel scalar bitmanip

#### selects RV64 address arithmetic for MIR get-element-pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_gep_module("rv64_gep_checked")))
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

#### selects RV64 JALR for MIR CallIndirect instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_call_indirect_module("rv64_call_indirect_checked")))
expect(count_opcode(block, RV_OP_JALR)).to_equal(1)
expect(has_opcode(block, RV_OP_CALL)).to_equal(false)
```

</details>

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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsupported = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(1), "bit_popcount", [virt_operand(0)])
expect(unsupported.insts.len()).to_equal(1)
expect(unsupported.insts[0].opcode).to_equal(RV_OP_NOP)
expect(unsupported.insts[0].operands.len()).to_equal(0)

val malformed = rv_select_scalar_bitmanip(new_isel_context(), virt_operand(1), BIT_ROTATE_LEFT, [virt_operand(0)])
expect(malformed.insts.len()).to_equal(1)
expect(malformed.insts[0].opcode).to_equal(RV_OP_NOP)
expect(malformed.insts[0].operands.len()).to_equal(0)
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

#### fails closed with RV64 NOP for unsupported MIR intrinsics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = entry_block(isel_module_riscv64(build_intrinsic_module("unsupported_intrinsic_test", "bit_popcount", 1)))
expect(count_opcode(block, RV_OP_NOP)).to_equal(1)
expect(first_operand_count(block, RV_OP_NOP)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native/isel_riscv64_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Isel Riscv64
- RV64 native ISel scalar bitmanip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
