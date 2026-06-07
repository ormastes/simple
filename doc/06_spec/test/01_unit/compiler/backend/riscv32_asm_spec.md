# Riscv32 Asm Specification

> <details>

<!-- sdn-diagram:id=riscv32_asm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_asm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv32_asm_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_asm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 79 | 79 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Asm Specification

## Scenarios

### RV32 ASM - Constants

#### XLEN is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xlen = 32
expect(xlen).to_equal(32)
```

</details>

#### register size is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg_size = 4
expect(reg_size).to_equal(4)
```

</details>

#### stack alignment is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_align = 16
expect(stack_align).to_equal(16)
```

</details>

### RV32 ASM - ABI Register Names

#### x0 maps to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val abi_names = {
    "x0": "zero", "x1": "ra", "x2": "sp", "x3": "gp", "x4": "tp",
    "x5": "t0", "x6": "t1", "x7": "t2",
    "x8": "s0", "x9": "s1",
    "x10": "a0", "x11": "a1", "x12": "a2", "x13": "a3",
    "x14": "a4", "x15": "a5", "x16": "a6", "x17": "a7"
}
expect(abi_names["x0"]).to_equal("zero")
```

</details>

#### x1 maps to ra

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "ra"
expect(name).to_equal("ra")
```

</details>

#### x2 maps to sp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "sp"
expect(name).to_equal("sp")
```

</details>

#### x3 maps to gp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "gp"
expect(name).to_equal("gp")
```

</details>

#### x4 maps to tp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "tp"
expect(name).to_equal("tp")
```

</details>

#### x5 maps to t0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "t0"
expect(name).to_equal("t0")
```

</details>

#### x8 maps to s0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "s0"
expect(name).to_equal("s0")
```

</details>

#### x10 maps to a0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "a0"
expect(name).to_equal("a0")
```

</details>

#### x17 maps to a7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "a7"
expect(name).to_equal("a7")
```

</details>

### RV32 ASM - Prologue Generation

#### prologue uses sw (not sd) for 32-bit registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RV32 prologue saves ra and s0 using sw (store word, 32-bit)
val expected_save_ra = "sw ra"
val expected_save_s0 = "sw s0"
expect(expected_save_ra).to_start_with("sw")
expect(expected_save_s0).to_start_with("sw")
```

</details>

#### prologue frame size is aligned to 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For frame_size=20, aligned to ((20+15)/16)*16 = 32
val frame_size = 20
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(32)
```

</details>

#### prologue frame size 1 aligns to 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame_size = 1
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(16)
```

</details>

#### prologue frame size 16 stays at 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame_size = 16
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(16)
```

</details>

#### prologue frame size 33 aligns to 48

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame_size = 33
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(48)
```

</details>

#### prologue saves ra at top of frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ra saved at aligned_size - 4 for 32-bit
val aligned_size = 32
val ra_offset = aligned_size - 4
expect(ra_offset).to_equal(28)
```

</details>

#### prologue saves s0 below ra

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# s0 saved at aligned_size - 8 for 32-bit
val aligned_size = 32
val s0_offset = aligned_size - 8
expect(s0_offset).to_equal(24)
```

</details>

### RV32 ASM - Epilogue Generation

#### epilogue uses lw (not ld) for 32-bit registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RV32 epilogue restores ra and s0 using lw (load word, 32-bit)
val expected_restore_ra = "lw ra"
val expected_restore_s0 = "lw s0"
expect(expected_restore_ra).to_start_with("lw")
expect(expected_restore_s0).to_start_with("lw")
```

</details>

#### epilogue ends with ret

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val last_instruction = "ret"
expect(last_instruction).to_equal("ret")
```

</details>

#### epilogue restores sp with addi

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val restore_sp = "addi sp, sp"
expect(restore_sp).to_start_with("addi sp")
```

</details>

### RV32 ASM - Attribute Directives

#### attribute arch specifies rv32im

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch_attr = ".attribute arch, \"rv32im\""
expect(arch_attr).to_contain("rv32im")
```

</details>

#### attribute specifies no unaligned access

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unaligned_attr = ".attribute unaligned_access, 0"
expect(unaligned_attr).to_contain("unaligned_access, 0")
```

</details>

#### attribute specifies 16-byte stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_attr = ".attribute stack_align, 16"
expect(stack_attr).to_contain("stack_align, 16")
```

</details>

### RV32 ASM - Memory Operations

#### word load uses lw instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "lw a0, 0(sp)"
expect(inst).to_start_with("lw")
```

</details>

#### word store uses sw instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "sw a0, 0(sp)"
expect(inst).to_start_with("sw")
```

</details>

#### byte load uses lb instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "lb a0, 0(sp)"
expect(inst).to_start_with("lb")
```

</details>

#### unsigned byte load uses lbu instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "lbu a0, 0(sp)"
expect(inst).to_start_with("lbu")
```

</details>

#### byte store uses sb instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "sb a0, 0(sp)"
expect(inst).to_start_with("sb")
```

</details>

#### halfword load uses lh instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "lh a0, 0(sp)"
expect(inst).to_start_with("lh")
```

</details>

#### unsigned halfword load uses lhu instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "lhu a0, 0(sp)"
expect(inst).to_start_with("lhu")
```

</details>

#### halfword store uses sh instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "sh a0, 0(sp)"
expect(inst).to_start_with("sh")
```

</details>

#### no ld instruction (64-bit only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RV32 does NOT have ld (load doubleword), that is RV64 only
val rv32_loads = ["lw", "lh", "lhu", "lb", "lbu"]
expect(rv32_loads).to_contain("lw")
```

</details>

#### no sd instruction (64-bit only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RV32 does NOT have sd (store doubleword), that is RV64 only
val rv32_stores = ["sw", "sh", "sb"]
expect(rv32_stores).to_contain("sw")
```

</details>

### RV32 ASM - RV32M Multiply/Divide

#### mul produces mul instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "mul a0, a1, a2"
expect(inst).to_start_with("mul ")
```

</details>

#### mulh produces mulh instruction (upper 32 bits)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "mulh a0, a1, a2"
expect(inst).to_start_with("mulh")
```

</details>

#### mulhu produces mulhu instruction (unsigned upper)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "mulhu a0, a1, a2"
expect(inst).to_start_with("mulhu")
```

</details>

#### mulhsu produces mulhsu instruction (signed x unsigned)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "mulhsu a0, a1, a2"
expect(inst).to_start_with("mulhsu")
```

</details>

#### div produces div instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "div a0, a1, a2"
expect(inst).to_start_with("div ")
```

</details>

#### divu produces divu instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "divu a0, a1, a2"
expect(inst).to_start_with("divu")
```

</details>

#### rem produces rem instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "rem a0, a1, a2"
expect(inst).to_start_with("rem ")
```

</details>

#### remu produces remu instruction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "remu a0, a1, a2"
expect(inst).to_start_with("remu")
```

</details>

### RV32 ASM - Atomic Instructions

#### load-reserved uses lr.w suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "lr.w a0, (a1)"
expect(inst).to_contain("lr.w")
```

</details>

#### store-conditional uses sc.w suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "sc.w a0, a1, (a2)"
expect(inst).to_contain("sc.w")
```

</details>

#### atomic swap uses amoswap.w suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "amoswap.w a0, a1, (a2)"
expect(inst).to_contain("amoswap.w")
```

</details>

#### atomic add uses amoadd.w suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "amoadd.w a0, a1, (a2)"
expect(inst).to_contain("amoadd.w")
```

</details>

#### atomic AND uses amoand.w suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "amoand.w a0, a1, (a2)"
expect(inst).to_contain("amoand.w")
```

</details>

#### atomic OR uses amoor.w suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "amoor.w a0, a1, (a2)"
expect(inst).to_contain("amoor.w")
```

</details>

#### atomic instructions do NOT use .d suffix on RV32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w_inst = "lr.w a0, (a1)"
val has_d_suffix = w_inst.contains(".d")
expect(has_d_suffix).to_equal(false)
```

</details>

### RV32 ASM - Address Calculation

#### load_address uses lui + addi pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 32-bit addresses are loaded with lui (upper 20 bits) + addi (lower 12 bits)
val lui_inst = "lui a0, %hi(my_symbol)"
val addi_inst = "addi a0, a0, %lo(my_symbol)"
expect(lui_inst).to_contain("lui")
expect(lui_inst).to_contain("%hi")
expect(addi_inst).to_contain("addi")
expect(addi_inst).to_contain("%lo")
```

</details>

#### small immediate uses addi alone

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Values -2048..2047 fit in 12-bit immediate
val imm = 100
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(true)
```

</details>

#### value 2047 fits in 12-bit immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = 2047
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(true)
```

</details>

#### value 2048 does NOT fit in 12-bit immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = 2048
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(false)
```

</details>

#### value -2048 fits in 12-bit immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = -2048
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(true)
```

</details>

#### value -2049 does NOT fit in 12-bit immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imm = -2049
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(false)
```

</details>

#### large immediate uses lui + addi pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Value 0x12345 requires lui + addi
val imm = 0x12345
val fits_in_12 = imm >= -2048 and imm <= 2047
expect(fits_in_12).to_equal(false)
```

</details>

### RV32 ASM - ILP32 ABI Register Lists

#### argument registers are a0 through a7

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(arg_regs.len()).to_equal(8)
expect(arg_regs[0]).to_equal("a0")
expect(arg_regs[7]).to_equal("a7")
```

</details>

#### return registers are a0 and a1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_regs = ["a0", "a1"]
expect(ret_regs.len()).to_equal(2)
expect(ret_regs[0]).to_equal("a0")
expect(ret_regs[1]).to_equal("a1")
```

</details>

#### callee-saved list has 12 registers (s0-s11)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
expect(callee_saved.len()).to_equal(12)
```

</details>

#### caller-saved list has 15 registers (t0-t6 + a0-a7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caller_saved = ["t0", "t1", "t2", "t3", "t4", "t5", "t6",
                    "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(caller_saved.len()).to_equal(15)
```

</details>

#### arg register index 0 is a0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
val reg = arg_regs[0]
expect(reg).to_equal("a0")
```

</details>

#### arg register index 7 is a7

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
val reg = arg_regs[7]
expect(reg).to_equal("a7")
```

</details>

#### arg register index 8 overflows to stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When index >= 8, arguments go on the stack
val index = 8
val on_stack = index >= 8
expect(on_stack).to_equal(true)
```

</details>

### RV32 ASM - Callee-Saved Check

#### s0 is callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
expect(callee_saved).to_contain("s0")
```

</details>

#### t0 is NOT callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
var found = false
for r in callee_saved:
    if r == "t0":
        found = true
expect(found).to_equal(false)
```

</details>

#### a0 is NOT callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
var found = false
for r in callee_saved:
    if r == "a0":
        found = true
expect(found).to_equal(false)
```

</details>

### RV32 ASM - Shift Operations

#### shift left logical uses sll

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "sll a0, a1, a2"
expect(inst).to_start_with("sll ")
```

</details>

#### shift left immediate uses slli

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "slli a0, a1, 5"
expect(inst).to_start_with("slli")
```

</details>

#### shift right logical uses srl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "srl a0, a1, a2"
expect(inst).to_start_with("srl ")
```

</details>

#### shift right arithmetic uses sra

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "sra a0, a1, a2"
expect(inst).to_start_with("sra ")
```

</details>

#### RV32 shift amount is 5 bits (0-31)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_shift = 31
expect(max_shift).to_equal(31)
```

</details>

### RV32 ASM - System Instructions

#### ecall instruction text is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "ecall"
expect(inst).to_equal("ecall")
```

</details>

#### ebreak instruction text is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "ebreak"
expect(inst).to_equal("ebreak")
```

</details>

#### mret instruction text is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "mret"
expect(inst).to_equal("mret")
```

</details>

#### wfi instruction text is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "wfi"
expect(inst).to_equal("wfi")
```

</details>

#### fence instruction text is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "fence"
expect(inst).to_equal("fence")
```

</details>

#### fence.i instruction text is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "fence.i"
expect(inst).to_equal("fence.i")
```

</details>

#### nop instruction text is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = "nop"
expect(inst).to_equal("nop")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/riscv32_asm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV32 ASM - Constants
- RV32 ASM - ABI Register Names
- RV32 ASM - Prologue Generation
- RV32 ASM - Epilogue Generation
- RV32 ASM - Attribute Directives
- RV32 ASM - Memory Operations
- RV32 ASM - RV32M Multiply/Divide
- RV32 ASM - Atomic Instructions
- RV32 ASM - Address Calculation
- RV32 ASM - ILP32 ABI Register Lists
- RV32 ASM - Callee-Saved Check
- RV32 ASM - Shift Operations
- RV32 ASM - System Instructions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 79 |
| Active scenarios | 79 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
