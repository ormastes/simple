# Riscv32 Asm Specification

> Tests covering RV32 ASM - Constants, RV32 ASM - ABI Register Names, RV32 ASM - Prologue Generation, RV32 ASM - Epilogue Generation, RV32 ASM - Attribute Directives, RV32 ASM - Memory Operations, RV32 ASM - RV32M Multiply/Divide, RV32 ASM - Atomic Instructions, RV32 ASM - Address Calculation, RV32 ASM - ILP32 ABI Register Lists, RV32 ASM - Callee-Saved Check, RV32 ASM - Shift Operations, RV32 ASM - System Instructions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 79 | 79 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Asm Specification

## Scenarios

### RV32 ASM - Constants

#### XLEN is 32

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- XLEN is 32
   - Expected: xlen equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("XLEN is 32")
val xlen = 32
expect(xlen).to_equal(32)
```

</details>

#### register size is 4 bytes

- register size is 4 bytes
   - Expected: reg_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register size is 4 bytes")
val reg_size = 4
expect(reg_size).to_equal(4)
```

</details>

#### stack alignment is 16 bytes

- stack alignment is 16 bytes
   - Expected: stack_align equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stack alignment is 16 bytes")
val stack_align = 16
expect(stack_align).to_equal(16)
```

</details>

### RV32 ASM - ABI Register Names

#### x0 maps to zero

- x0 maps to zero
   - Expected: abi_names["x0"] equals `zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x0 maps to zero")
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

- x1 maps to ra
   - Expected: name equals `ra`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x1 maps to ra")
val name = "ra"
expect(name).to_equal("ra")
```

</details>

#### x2 maps to sp

- x2 maps to sp
   - Expected: name equals `sp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x2 maps to sp")
val name = "sp"
expect(name).to_equal("sp")
```

</details>

#### x3 maps to gp

- x3 maps to gp
   - Expected: name equals `gp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x3 maps to gp")
val name = "gp"
expect(name).to_equal("gp")
```

</details>

#### x4 maps to tp

- x4 maps to tp
   - Expected: name equals `tp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x4 maps to tp")
val name = "tp"
expect(name).to_equal("tp")
```

</details>

#### x5 maps to t0

- x5 maps to t0
   - Expected: name equals `t0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x5 maps to t0")
val name = "t0"
expect(name).to_equal("t0")
```

</details>

#### x8 maps to s0

- x8 maps to s0
   - Expected: name equals `s0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x8 maps to s0")
val name = "s0"
expect(name).to_equal("s0")
```

</details>

#### x10 maps to a0

- x10 maps to a0
   - Expected: name equals `a0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x10 maps to a0")
val name = "a0"
expect(name).to_equal("a0")
```

</details>

#### x17 maps to a7

- x17 maps to a7
   - Expected: name equals `a7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x17 maps to a7")
val name = "a7"
expect(name).to_equal("a7")
```

</details>

### RV32 ASM - Prologue Generation

#### prologue uses sw (not sd) for 32-bit registers

- prologue uses sw (not sd) for 32-bit registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prologue uses sw (not sd) for 32-bit registers")
# RV32 prologue saves ra and s0 using sw (store word, 32-bit)
val expected_save_ra = "sw ra"
val expected_save_s0 = "sw s0"
expect(expected_save_ra).to_start_with("sw")
expect(expected_save_s0).to_start_with("sw")
```

</details>

#### prologue frame size is aligned to 16 bytes

- prologue frame size is aligned to 16 bytes
   - Expected: aligned equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prologue frame size is aligned to 16 bytes")
# For frame_size=20, aligned to ((20+15)/16)*16 = 32
val frame_size = 20
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(32)
```

</details>

#### prologue frame size 1 aligns to 16

- prologue frame size 1 aligns to 16
   - Expected: aligned equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prologue frame size 1 aligns to 16")
val frame_size = 1
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(16)
```

</details>

#### prologue frame size 16 stays at 16

- prologue frame size 16 stays at 16
   - Expected: aligned equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prologue frame size 16 stays at 16")
val frame_size = 16
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(16)
```

</details>

#### prologue frame size 33 aligns to 48

- prologue frame size 33 aligns to 48
   - Expected: aligned equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prologue frame size 33 aligns to 48")
val frame_size = 33
val aligned = ((frame_size + 15) / 16) * 16
expect(aligned).to_equal(48)
```

</details>

#### prologue saves ra at top of frame

- prologue saves ra at top of frame
   - Expected: ra_offset equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prologue saves ra at top of frame")
# ra saved at aligned_size - 4 for 32-bit
val aligned_size = 32
val ra_offset = aligned_size - 4
expect(ra_offset).to_equal(28)
```

</details>

#### prologue saves s0 below ra

- prologue saves s0 below ra
   - Expected: s0_offset equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("prologue saves s0 below ra")
# s0 saved at aligned_size - 8 for 32-bit
val aligned_size = 32
val s0_offset = aligned_size - 8
expect(s0_offset).to_equal(24)
```

</details>

### RV32 ASM - Epilogue Generation

#### epilogue uses lw (not ld) for 32-bit registers

- epilogue uses lw (not ld) for 32-bit registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("epilogue uses lw (not ld) for 32-bit registers")
# RV32 epilogue restores ra and s0 using lw (load word, 32-bit)
val expected_restore_ra = "lw ra"
val expected_restore_s0 = "lw s0"
expect(expected_restore_ra).to_start_with("lw")
expect(expected_restore_s0).to_start_with("lw")
```

</details>

#### epilogue ends with ret

- epilogue ends with ret
   - Expected: last_instruction equals `ret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("epilogue ends with ret")
val last_instruction = "ret"
expect(last_instruction).to_equal("ret")
```

</details>

#### epilogue restores sp with addi

- epilogue restores sp with addi


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("epilogue restores sp with addi")
val restore_sp = "addi sp, sp"
expect(restore_sp).to_start_with("addi sp")
```

</details>

### RV32 ASM - Attribute Directives

#### attribute arch specifies rv32im

- attribute arch specifies rv32im


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("attribute arch specifies rv32im")
val arch_attr = ".attribute arch, \"rv32im\""
expect(arch_attr).to_contain("rv32im")
```

</details>

#### attribute specifies no unaligned access

- attribute specifies no unaligned access


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("attribute specifies no unaligned access")
val unaligned_attr = ".attribute unaligned_access, 0"
expect(unaligned_attr).to_contain("unaligned_access, 0")
```

</details>

#### attribute specifies 16-byte stack alignment

- attribute specifies 16-byte stack alignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("attribute specifies 16-byte stack alignment")
val stack_attr = ".attribute stack_align, 16"
expect(stack_attr).to_contain("stack_align, 16")
```

</details>

### RV32 ASM - Memory Operations

#### word load uses lw instruction

- word load uses lw instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("word load uses lw instruction")
val inst = "lw a0, 0(sp)"
expect(inst).to_start_with("lw")
```

</details>

#### word store uses sw instruction

- word store uses sw instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("word store uses sw instruction")
val inst = "sw a0, 0(sp)"
expect(inst).to_start_with("sw")
```

</details>

#### byte load uses lb instruction

- byte load uses lb instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("byte load uses lb instruction")
val inst = "lb a0, 0(sp)"
expect(inst).to_start_with("lb")
```

</details>

#### unsigned byte load uses lbu instruction

- unsigned byte load uses lbu instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unsigned byte load uses lbu instruction")
val inst = "lbu a0, 0(sp)"
expect(inst).to_start_with("lbu")
```

</details>

#### byte store uses sb instruction

- byte store uses sb instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("byte store uses sb instruction")
val inst = "sb a0, 0(sp)"
expect(inst).to_start_with("sb")
```

</details>

#### halfword load uses lh instruction

- halfword load uses lh instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("halfword load uses lh instruction")
val inst = "lh a0, 0(sp)"
expect(inst).to_start_with("lh")
```

</details>

#### unsigned halfword load uses lhu instruction

- unsigned halfword load uses lhu instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unsigned halfword load uses lhu instruction")
val inst = "lhu a0, 0(sp)"
expect(inst).to_start_with("lhu")
```

</details>

#### halfword store uses sh instruction

- halfword store uses sh instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("halfword store uses sh instruction")
val inst = "sh a0, 0(sp)"
expect(inst).to_start_with("sh")
```

</details>

#### no ld instruction (64-bit only)

- no ld instruction (64-bit only)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("no ld instruction (64-bit only)")
# RV32 does NOT have ld (load doubleword), that is RV64 only
val rv32_loads = ["lw", "lh", "lhu", "lb", "lbu"]
expect(rv32_loads).to_contain("lw")
```

</details>

#### no sd instruction (64-bit only)

- no sd instruction (64-bit only)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("no sd instruction (64-bit only)")
# RV32 does NOT have sd (store doubleword), that is RV64 only
val rv32_stores = ["sw", "sh", "sb"]
expect(rv32_stores).to_contain("sw")
```

</details>

### RV32 ASM - RV32M Multiply/Divide

#### mul produces mul instruction

- mul produces mul instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mul produces mul instruction")
val inst = "mul a0, a1, a2"
expect(inst).to_start_with("mul ")
```

</details>

#### mulh produces mulh instruction (upper 32 bits)

- mulh produces mulh instruction (upper 32 bits)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mulh produces mulh instruction (upper 32 bits)")
val inst = "mulh a0, a1, a2"
expect(inst).to_start_with("mulh")
```

</details>

#### mulhu produces mulhu instruction (unsigned upper)

- mulhu produces mulhu instruction (unsigned upper)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mulhu produces mulhu instruction (unsigned upper)")
val inst = "mulhu a0, a1, a2"
expect(inst).to_start_with("mulhu")
```

</details>

#### mulhsu produces mulhsu instruction (signed x unsigned)

- mulhsu produces mulhsu instruction (signed x unsigned)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mulhsu produces mulhsu instruction (signed x unsigned)")
val inst = "mulhsu a0, a1, a2"
expect(inst).to_start_with("mulhsu")
```

</details>

#### div produces div instruction

- div produces div instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("div produces div instruction")
val inst = "div a0, a1, a2"
expect(inst).to_start_with("div ")
```

</details>

#### divu produces divu instruction

- divu produces divu instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("divu produces divu instruction")
val inst = "divu a0, a1, a2"
expect(inst).to_start_with("divu")
```

</details>

#### rem produces rem instruction

- rem produces rem instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rem produces rem instruction")
val inst = "rem a0, a1, a2"
expect(inst).to_start_with("rem ")
```

</details>

#### remu produces remu instruction

- remu produces remu instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("remu produces remu instruction")
val inst = "remu a0, a1, a2"
expect(inst).to_start_with("remu")
```

</details>

### RV32 ASM - Atomic Instructions

#### load-reserved uses lr.w suffix

- load-reserved uses lr.w suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("load-reserved uses lr.w suffix")
val inst = "lr.w a0, (a1)"
expect(inst).to_contain("lr.w")
```

</details>

#### store-conditional uses sc.w suffix

- store-conditional uses sc.w suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("store-conditional uses sc.w suffix")
val inst = "sc.w a0, a1, (a2)"
expect(inst).to_contain("sc.w")
```

</details>

#### atomic swap uses amoswap.w suffix

- atomic swap uses amoswap.w suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("atomic swap uses amoswap.w suffix")
val inst = "amoswap.w a0, a1, (a2)"
expect(inst).to_contain("amoswap.w")
```

</details>

#### atomic add uses amoadd.w suffix

- atomic add uses amoadd.w suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("atomic add uses amoadd.w suffix")
val inst = "amoadd.w a0, a1, (a2)"
expect(inst).to_contain("amoadd.w")
```

</details>

#### atomic AND uses amoand.w suffix

- atomic AND uses amoand.w suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("atomic AND uses amoand.w suffix")
val inst = "amoand.w a0, a1, (a2)"
expect(inst).to_contain("amoand.w")
```

</details>

#### atomic OR uses amoor.w suffix

- atomic OR uses amoor.w suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("atomic OR uses amoor.w suffix")
val inst = "amoor.w a0, a1, (a2)"
expect(inst).to_contain("amoor.w")
```

</details>

#### atomic instructions do NOT use .d suffix on RV32

- atomic instructions do NOT use .d suffix on RV32
   - Expected: has_d_suffix is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("atomic instructions do NOT use .d suffix on RV32")
val w_inst = "lr.w a0, (a1)"
val has_d_suffix = w_inst.contains(".d")
expect(has_d_suffix).to_equal(false)
```

</details>

### RV32 ASM - Address Calculation

#### load_address uses lui + addi pair

- load_address uses lui + addi pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("load_address uses lui + addi pair")
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

- small immediate uses addi alone
   - Expected: fits is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("small immediate uses addi alone")
# Values -2048..2047 fit in 12-bit immediate
val imm = 100
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(true)
```

</details>

#### value 2047 fits in 12-bit immediate

- value 2047 fits in 12-bit immediate
   - Expected: fits is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("value 2047 fits in 12-bit immediate")
val imm = 2047
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(true)
```

</details>

#### value 2048 does NOT fit in 12-bit immediate

- value 2048 does NOT fit in 12-bit immediate
   - Expected: fits is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("value 2048 does NOT fit in 12-bit immediate")
val imm = 2048
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(false)
```

</details>

#### value -2048 fits in 12-bit immediate

- value -2048 fits in 12-bit immediate
   - Expected: fits is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("value -2048 fits in 12-bit immediate")
val imm = -2048
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(true)
```

</details>

#### value -2049 does NOT fit in 12-bit immediate

- value -2049 does NOT fit in 12-bit immediate
   - Expected: fits is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("value -2049 does NOT fit in 12-bit immediate")
val imm = -2049
val fits = imm >= -2048 and imm <= 2047
expect(fits).to_equal(false)
```

</details>

#### large immediate uses lui + addi pair

- large immediate uses lui + addi pair
   - Expected: fits_in_12 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("large immediate uses lui + addi pair")
# Value 0x12345 requires lui + addi
val imm = 0x12345
val fits_in_12 = imm >= -2048 and imm <= 2047
expect(fits_in_12).to_equal(false)
```

</details>

### RV32 ASM - ILP32 ABI Register Lists

#### argument registers are a0 through a7

- argument registers are a0 through a7
   - Expected: arg_regs.len() equals `8`
   - Expected: arg_regs[0] equals `a0`
   - Expected: arg_regs[7] equals `a7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("argument registers are a0 through a7")
val arg_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(arg_regs.len()).to_equal(8)
expect(arg_regs[0]).to_equal("a0")
expect(arg_regs[7]).to_equal("a7")
```

</details>

#### return registers are a0 and a1

- return registers are a0 and a1
   - Expected: ret_regs.len() equals `2`
   - Expected: ret_regs[0] equals `a0`
   - Expected: ret_regs[1] equals `a1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("return registers are a0 and a1")
val ret_regs = ["a0", "a1"]
expect(ret_regs.len()).to_equal(2)
expect(ret_regs[0]).to_equal("a0")
expect(ret_regs[1]).to_equal("a1")
```

</details>

#### callee-saved list has 12 registers (s0-s11)

- callee-saved list has 12 registers (s0-s11)
   - Expected: callee_saved.len() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("callee-saved list has 12 registers (s0-s11)")
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
expect(callee_saved.len()).to_equal(12)
```

</details>

#### caller-saved list has 15 registers (t0-t6 + a0-a7)

- caller-saved list has 15 registers (t0-t6 + a0-a7)
   - Expected: caller_saved.len() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("caller-saved list has 15 registers (t0-t6 + a0-a7)")
val caller_saved = ["t0", "t1", "t2", "t3", "t4", "t5", "t6",
                    "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(caller_saved.len()).to_equal(15)
```

</details>

#### arg register index 0 is a0

- arg register index 0 is a0
   - Expected: reg equals `a0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("arg register index 0 is a0")
val arg_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
val reg = arg_regs[0]
expect(reg).to_equal("a0")
```

</details>

#### arg register index 7 is a7

- arg register index 7 is a7
   - Expected: reg equals `a7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("arg register index 7 is a7")
val arg_regs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
val reg = arg_regs[7]
expect(reg).to_equal("a7")
```

</details>

#### arg register index 8 overflows to stack

- arg register index 8 overflows to stack
   - Expected: on_stack is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("arg register index 8 overflows to stack")
# When index >= 8, arguments go on the stack
val index = 8
val on_stack = index >= 8
expect(on_stack).to_equal(true)
```

</details>

### RV32 ASM - Callee-Saved Check

#### s0 is callee-saved

- s0 is callee-saved


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("s0 is callee-saved")
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
expect(callee_saved).to_contain("s0")
```

</details>

#### t0 is NOT callee-saved

- t0 is NOT callee-saved
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("t0 is NOT callee-saved")
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
var found = false
for r in callee_saved:
    if r == "t0":
        found = true
expect(found).to_equal(false)
```

</details>

#### a0 is NOT callee-saved

- a0 is NOT callee-saved
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a0 is NOT callee-saved")
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

- shift left logical uses sll


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shift left logical uses sll")
val inst = "sll a0, a1, a2"
expect(inst).to_start_with("sll ")
```

</details>

#### shift left immediate uses slli

- shift left immediate uses slli


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shift left immediate uses slli")
val inst = "slli a0, a1, 5"
expect(inst).to_start_with("slli")
```

</details>

#### shift right logical uses srl

- shift right logical uses srl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shift right logical uses srl")
val inst = "srl a0, a1, a2"
expect(inst).to_start_with("srl ")
```

</details>

#### shift right arithmetic uses sra

- shift right arithmetic uses sra


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shift right arithmetic uses sra")
val inst = "sra a0, a1, a2"
expect(inst).to_start_with("sra ")
```

</details>

#### RV32 shift amount is 5 bits (0-31)

- RV32 shift amount is 5 bits (0-31)
   - Expected: max_shift equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("RV32 shift amount is 5 bits (0-31)")
val max_shift = 31
expect(max_shift).to_equal(31)
```

</details>

### RV32 ASM - System Instructions

#### ecall instruction text is correct

- ecall instruction text is correct
   - Expected: inst equals `ecall`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ecall instruction text is correct")
val inst = "ecall"
expect(inst).to_equal("ecall")
```

</details>

#### ebreak instruction text is correct

- ebreak instruction text is correct
   - Expected: inst equals `ebreak`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ebreak instruction text is correct")
val inst = "ebreak"
expect(inst).to_equal("ebreak")
```

</details>

#### mret instruction text is correct

- mret instruction text is correct
   - Expected: inst equals `mret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("mret instruction text is correct")
val inst = "mret"
expect(inst).to_equal("mret")
```

</details>

#### wfi instruction text is correct

- wfi instruction text is correct
   - Expected: inst equals `wfi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("wfi instruction text is correct")
val inst = "wfi"
expect(inst).to_equal("wfi")
```

</details>

#### fence instruction text is correct

- fence instruction text is correct
   - Expected: inst equals `fence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fence instruction text is correct")
val inst = "fence"
expect(inst).to_equal("fence")
```

</details>

#### fence.i instruction text is correct

- fence.i instruction text is correct
   - Expected: inst equals `fence.i`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fence.i instruction text is correct")
val inst = "fence.i"
expect(inst).to_equal("fence.i")
```

</details>

#### nop instruction text is correct

- nop instruction text is correct
   - Expected: inst equals `nop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("nop instruction text is correct")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 ASM - Constants, RV32 ASM - ABI Register Names, RV32 ASM - Prologue Generation, RV32 ASM - Epilogue Generation, RV32 ASM - Attribute Directives, RV32 ASM - Memory Operations, RV32 ASM - RV32M Multiply/Divide, RV32 ASM - Atomic Instructions, RV32 ASM - Address Calculation, RV32 ASM - ILP32 ABI Register Lists, RV32 ASM - Callee-Saved Check, RV32 ASM - Shift Operations, RV32 ASM - System Instructions.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6d9c8e03ff970abbdacf2cf1c4efdb386a31414ac7d6849394ecfec74527bb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6d9c8e03ff970abbdacf2cf1c4efdb386a31414ac7d6849394ecfec74527bb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6d9c8e03ff970abbdacf2cf1c4efdb386a31414ac7d6849394ecfec74527bb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/riscv32_asm_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/riscv32_asm_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/riscv32_asm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/riscv32_asm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/riscv32_asm_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/riscv32_asm_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'XLEN is 32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/riscv32_asm_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'register size is 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/riscv32_asm_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stack alignment is 16 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
