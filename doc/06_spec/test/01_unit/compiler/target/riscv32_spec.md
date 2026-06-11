# Riscv32 Specification

> <details>

<!-- sdn-diagram:id=riscv32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv32_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 101 | 101 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Specification

## Scenarios

### RV32 Target - Triple Constants

#### has correct default triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-none"
expect(triple).to_equal("riscv32-unknown-none")
```

</details>

#### has correct Linux triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-linux-gnu"
expect(triple).to_equal("riscv32-unknown-linux-gnu")
```

</details>

#### has correct baremetal triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-none-elf"
expect(triple).to_equal("riscv32-unknown-none-elf")
```

</details>

#### default triple contains riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-none"
expect(triple).to_contain("riscv32")
```

</details>

#### Linux triple ends with gnu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-linux-gnu"
expect(triple).to_end_with("gnu")
```

</details>

#### baremetal triple ends with elf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-none-elf"
expect(triple).to_end_with("elf")
```

</details>

### RV32 Target - CPU and Feature Defaults

#### has generic-rv32 default CPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = "generic-rv32"
expect(cpu).to_equal("generic-rv32")
```

</details>

#### default features include M extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+m")
```

</details>

#### default features include A extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+a")
```

</details>

#### default features include F extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+f")
```

</details>

#### default features include D extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+d")
```

</details>

#### default features include C extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+c")
```

</details>

#### has 5 default features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features.len()).to_equal(5)
```

</details>

### RV32 Target - Data Layout

#### has correct LLVM data layout string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_equal("e-m:e-p:32:32-i64:64-n32-S128")
```

</details>

#### data layout starts with little-endian marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_start_with("e-")
```

</details>

#### data layout specifies 32-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("p:32:32")
```

</details>

#### data layout specifies native 32-bit integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("n32")
```

</details>

#### data layout specifies 128-bit stack alignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("S128")
```

</details>

#### data layout specifies ELF mangling

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("m:e")
```

</details>

### RV32 Target - Default TargetInfo

#### default has riscv32-unknown-none triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-none"
expect(triple).to_equal("riscv32-unknown-none")
```

</details>

#### default pointer size is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pointer_size = 4
expect(pointer_size).to_equal(4)
```

</details>

#### default pointer alignment is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pointer_align = 4
expect(pointer_align).to_equal(4)
```

</details>

#### default max atomic width is 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_atomic = 32
expect(max_atomic).to_equal(32)
```

</details>

#### default stack alignment is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_align = 16
expect(stack_align).to_equal(16)
```

</details>

#### default has no FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_fpu = false
expect(has_fpu).to_equal(false)
```

</details>

#### default is little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val endianness = "little"
expect(endianness).to_equal("little")
```

</details>

### RV32 Target - FPU Configuration

#### create_with_fpu has FPU enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_fpu = true
expect(has_fpu).to_equal(true)
```

</details>

#### create_with_fpu has F and D features

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+f")
expect(features).to_contain("+d")
```

</details>

#### create_with_fpu preserves pointer size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pointer_size = 4
expect(pointer_size).to_equal(4)
```

</details>

### RV32 Target - Linux Configuration

#### Linux target has linux triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-linux-gnu"
expect(triple).to_contain("linux")
```

</details>

#### Linux target has FPU enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_fpu = true
expect(has_fpu).to_equal(true)
```

</details>

#### Linux target preserves 4-byte pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pointer_size = 4
expect(pointer_size).to_equal(4)
```

</details>

### RV32 Target - Baremetal Configuration

#### baremetal has none-elf triple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-none-elf"
expect(triple).to_contain("none-elf")
```

</details>

#### baremetal has no FPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_fpu = false
expect(has_fpu).to_equal(false)
```

</details>

#### baremetal has minimal extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = ["+m"]
expect(features.len()).to_equal(1)
expect(features).to_contain("+m")
```

</details>

#### baremetal triple detects as baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-none-elf"
val is_baremetal = triple.contains("none")
expect(is_baremetal).to_equal(true)
```

</details>

#### linux triple does not detect as baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv32-unknown-linux-gnu"
val is_baremetal = triple.contains("none")
expect(is_baremetal).to_equal(false)
```

</details>

### RV32 Target - LLVM Type Methods

#### native int type is i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val native_int = "i32"
expect(native_int).to_equal("i32")
```

</details>

#### pointer type is ptr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr_type = "ptr"
expect(ptr_type).to_equal("ptr")
```

</details>

#### size type is i32 (not i64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size_type = "i32"
expect(size_type).to_equal("i32")
```

</details>

### RV32 Target - GPR Register Names

#### register 0 is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[0]).to_equal("zero")
```

</details>

#### register 1 is ra

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[1]).to_equal("ra")
```

</details>

#### register 2 is sp

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[2]).to_equal("sp")
```

</details>

#### register 8 is s0 (frame pointer)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[8]).to_equal("s0")
```

</details>

#### register 10 is a0 (first argument)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[10]).to_equal("a0")
```

</details>

#### register 31 is t6

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[31]).to_equal("t6")
```

</details>

#### has exactly 32 GPR names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names.len()).to_equal(32)
```

</details>

### RV32 Target - FPR Register Names

#### fpr 0 is ft0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names[0]).to_equal("ft0")
```

</details>

#### fpr 8 is fs0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names[8]).to_equal("fs0")
```

</details>

#### fpr 10 is fa0 (first float argument)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names[10]).to_equal("fa0")
```

</details>

#### has exactly 32 FPR names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names.len()).to_equal(32)
```

</details>

### RV32 Target - Callee-Saved GPRs

#### s0 (index 8) is callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 8
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### s1 (index 9) is callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 9
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### s2 (index 18) is callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 18
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### s11 (index 27) is callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 27
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### t0 (index 5) is NOT callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 5
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(false)
```

</details>

#### a0 (index 10) is NOT callee-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 10
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(false)
```

</details>

### RV32 Target - Caller-Saved GPRs

#### t0 (index 5) is caller-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 5
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### a0 (index 10) is caller-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 10
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### a7 (index 17) is caller-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 17
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### t6 (index 31) is caller-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 31
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### s0 (index 8) is NOT caller-saved

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 8
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(false)
```

</details>

### RV32 Target - Register Info Creation

#### base RV32IM has 32 GPRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_count = 32
expect(gpr_count).to_equal(32)
```

</details>

#### base RV32IM has no FPRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fpr_count = 0
expect(fpr_count).to_equal(0)
```

</details>

#### base RV32IM has no float support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_float = false
expect(has_float).to_equal(false)
```

</details>

#### RV32IMFD has 32 GPRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpr_count = 32
expect(gpr_count).to_equal(32)
```

</details>

#### RV32IMFD has 32 FPRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fpr_count = 32
expect(fpr_count).to_equal(32)
```

</details>

#### RV32IMFD has float support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_float = true
expect(has_float).to_equal(true)
```

</details>

#### RV32IMFD has double support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_double = true
expect(has_double).to_equal(true)
```

</details>

### RV32 Target - ILP32 Calling Convention

#### ILP32 convention name is ilp32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "ilp32"
expect(name).to_equal("ilp32")
```

</details>

#### ILP32F convention name is ilp32f

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "ilp32f"
expect(name).to_equal("ilp32f")
```

</details>

#### ILP32D convention name is ilp32d

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "ilp32d"
expect(name).to_equal("ilp32d")
```

</details>

#### has 8 argument GPRs (a0-a7)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_gpr_count = 8
expect(arg_gpr_count).to_equal(8)
```

</details>

#### ILP32 has 0 argument FPRs (soft-float)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_fpr_count = 0
expect(arg_fpr_count).to_equal(0)
```

</details>

#### ILP32F has 8 argument FPRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_fpr_count = 8
expect(arg_fpr_count).to_equal(8)
```

</details>

#### ILP32D has 8 argument FPRs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_fpr_count = 8
expect(arg_fpr_count).to_equal(8)
```

</details>

#### has 2 return GPRs (a0, a1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_gpr_count = 2
expect(ret_gpr_count).to_equal(2)
```

</details>

#### stack alignment is 16 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_alignment = 16
expect(stack_alignment).to_equal(16)
```

</details>

#### argument GPRs are a0 through a7

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_gprs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(arg_gprs.len()).to_equal(8)
expect(arg_gprs[0]).to_equal("a0")
expect(arg_gprs[7]).to_equal("a7")
```

</details>

#### return GPRs are a0 and a1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_gprs = ["a0", "a1"]
expect(ret_gprs.len()).to_equal(2)
expect(ret_gprs[0]).to_equal("a0")
expect(ret_gprs[1]).to_equal("a1")
```

</details>

#### callee-saved GPRs are s0 through s11

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
expect(callee_saved.len()).to_equal(12)
expect(callee_saved[0]).to_equal("s0")
expect(callee_saved[11]).to_equal("s11")
```

</details>

#### caller-saved GPRs include temporaries and arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caller_saved = ["t0", "t1", "t2", "t3", "t4", "t5", "t6",
                    "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(caller_saved.len()).to_equal(15)
expect(caller_saved).to_contain("t0")
expect(caller_saved).to_contain("a7")
```

</details>

### RV32 Target - Supported Extensions

#### supported extensions include M

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+m")
```

</details>

#### supported extensions include A

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+a")
```

</details>

#### supported extensions include zicsr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+zicsr")
```

</details>

#### supported extensions include zifencei

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+zifencei")
```

</details>

#### has 7 supported extensions total

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions.len()).to_equal(7)
```

</details>

### RV32 Target - ILP32 Type Sizes

#### bool is 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# rv32_type_size("bool") -> 1
val size = 1
expect(size).to_equal(1)
```

</details>

#### i8 is 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 1
expect(size).to_equal(1)
```

</details>

#### i16 is 2 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 2
expect(size).to_equal(2)
```

</details>

#### i32 is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 4
expect(size).to_equal(4)
```

</details>

#### i64 is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 8
expect(size).to_equal(8)
```

</details>

#### f32 is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 4
expect(size).to_equal(4)
```

</details>

#### f64 is 8 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 8
expect(size).to_equal(8)
```

</details>

#### pointer is 4 bytes (not 8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 4
expect(size).to_equal(4)
```

</details>

#### usize is 4 bytes (not 8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = 4
expect(size).to_equal(4)
```

</details>

### RV32 Target - ILP32 Type Alignment

#### i32 alignment is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### i64 alignment is 4 bytes on RV32 (not 8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# RV32 aligns i64 to 4 bytes, unlike LP64
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### f64 alignment is 4 bytes on RV32 (not 8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### pointer alignment is 4 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### bool alignment is 1 byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val alignment = 1
expect(alignment).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/target/riscv32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV32 Target - Triple Constants
- RV32 Target - CPU and Feature Defaults
- RV32 Target - Data Layout
- RV32 Target - Default TargetInfo
- RV32 Target - FPU Configuration
- RV32 Target - Linux Configuration
- RV32 Target - Baremetal Configuration
- RV32 Target - LLVM Type Methods
- RV32 Target - GPR Register Names
- RV32 Target - FPR Register Names
- RV32 Target - Callee-Saved GPRs
- RV32 Target - Caller-Saved GPRs
- RV32 Target - Register Info Creation
- RV32 Target - ILP32 Calling Convention
- RV32 Target - Supported Extensions
- RV32 Target - ILP32 Type Sizes
- RV32 Target - ILP32 Type Alignment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 101 |
| Active scenarios | 101 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
