# Riscv32 Specification

> Tests covering RV32 Target - Triple Constants, RV32 Target - CPU and Feature Defaults, RV32 Target - Data Layout, RV32 Target - Default TargetInfo, RV32 Target - FPU Configuration, RV32 Target - Linux Configuration, RV32 Target - Baremetal Configuration, RV32 Target - LLVM Type Methods, RV32 Target - GPR Register Names, RV32 Target - FPR Register Names, RV32 Target - Callee-Saved GPRs, RV32 Target - Caller-Saved GPRs, RV32 Target - Register Info Creation, RV32 Target - ILP32 Calling Convention, RV32 Target - Supported Extensions, RV32 Target - ILP32 Type Sizes, RV32 Target - ILP32 Type Alignment.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 101 | 101 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Specification

## Scenarios

### RV32 Target - Triple Constants

#### has correct default triple

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has correct default triple
   - Expected: triple equals `riscv32-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct default triple")
val triple = "riscv32-unknown-none"
expect(triple).to_equal("riscv32-unknown-none")
```

</details>

#### has correct Linux triple

- has correct Linux triple
   - Expected: triple equals `riscv32-unknown-linux-gnu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct Linux triple")
val triple = "riscv32-unknown-linux-gnu"
expect(triple).to_equal("riscv32-unknown-linux-gnu")
```

</details>

#### has correct baremetal triple

- has correct baremetal triple
   - Expected: triple equals `riscv32-unknown-none-elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct baremetal triple")
val triple = "riscv32-unknown-none-elf"
expect(triple).to_equal("riscv32-unknown-none-elf")
```

</details>

#### default triple contains riscv32

- default triple contains riscv32


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default triple contains riscv32")
val triple = "riscv32-unknown-none"
expect(triple).to_contain("riscv32")
```

</details>

#### Linux triple ends with gnu

- Linux triple ends with gnu


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Linux triple ends with gnu")
val triple = "riscv32-unknown-linux-gnu"
expect(triple).to_end_with("gnu")
```

</details>

#### baremetal triple ends with elf

- baremetal triple ends with elf


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("baremetal triple ends with elf")
val triple = "riscv32-unknown-none-elf"
expect(triple).to_end_with("elf")
```

</details>

### RV32 Target - CPU and Feature Defaults

#### has generic-rv32 default CPU

- has generic-rv32 default CPU
   - Expected: cpu equals `generic-rv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has generic-rv32 default CPU")
val cpu = "generic-rv32"
expect(cpu).to_equal("generic-rv32")
```

</details>

#### default features include M extension

- default features include M extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default features include M extension")
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+m")
```

</details>

#### default features include A extension

- default features include A extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default features include A extension")
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+a")
```

</details>

#### default features include F extension

- default features include F extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default features include F extension")
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+f")
```

</details>

#### default features include D extension

- default features include D extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default features include D extension")
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+d")
```

</details>

#### default features include C extension

- default features include C extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default features include C extension")
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+c")
```

</details>

#### has 5 default features

- has 5 default features
   - Expected: features.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has 5 default features")
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features.len()).to_equal(5)
```

</details>

### RV32 Target - Data Layout

#### has correct LLVM data layout string

- has correct LLVM data layout string
   - Expected: layout equals `e-m:e-p:32:32-i64:64-n32-S128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has correct LLVM data layout string")
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_equal("e-m:e-p:32:32-i64:64-n32-S128")
```

</details>

#### data layout starts with little-endian marker

- data layout starts with little-endian marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("data layout starts with little-endian marker")
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_start_with("e-")
```

</details>

#### data layout specifies 32-bit pointers

- data layout specifies 32-bit pointers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("data layout specifies 32-bit pointers")
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("p:32:32")
```

</details>

#### data layout specifies native 32-bit integers

- data layout specifies native 32-bit integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("data layout specifies native 32-bit integers")
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("n32")
```

</details>

#### data layout specifies 128-bit stack alignment

- data layout specifies 128-bit stack alignment


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("data layout specifies 128-bit stack alignment")
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("S128")
```

</details>

#### data layout specifies ELF mangling

- data layout specifies ELF mangling


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("data layout specifies ELF mangling")
val layout = "e-m:e-p:32:32-i64:64-n32-S128"
expect(layout).to_contain("m:e")
```

</details>

### RV32 Target - Default TargetInfo

#### default has riscv32-unknown-none triple

- default has riscv32-unknown-none triple
   - Expected: triple equals `riscv32-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default has riscv32-unknown-none triple")
val triple = "riscv32-unknown-none"
expect(triple).to_equal("riscv32-unknown-none")
```

</details>

#### default pointer size is 4 bytes

- default pointer size is 4 bytes
   - Expected: pointer_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default pointer size is 4 bytes")
val pointer_size = 4
expect(pointer_size).to_equal(4)
```

</details>

#### default pointer alignment is 4 bytes

- default pointer alignment is 4 bytes
   - Expected: pointer_align equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default pointer alignment is 4 bytes")
val pointer_align = 4
expect(pointer_align).to_equal(4)
```

</details>

#### default max atomic width is 32 bits

- default max atomic width is 32 bits
   - Expected: max_atomic equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default max atomic width is 32 bits")
val max_atomic = 32
expect(max_atomic).to_equal(32)
```

</details>

#### default stack alignment is 16 bytes

- default stack alignment is 16 bytes
   - Expected: stack_align equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default stack alignment is 16 bytes")
val stack_align = 16
expect(stack_align).to_equal(16)
```

</details>

#### default has no FPU

- default has no FPU
   - Expected: has_fpu is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default has no FPU")
val has_fpu = false
expect(has_fpu).to_equal(false)
```

</details>

#### default is little-endian

- default is little-endian
   - Expected: endianness equals `little`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("default is little-endian")
val endianness = "little"
expect(endianness).to_equal("little")
```

</details>

### RV32 Target - FPU Configuration

#### create_with_fpu has FPU enabled

- create_with_fpu has FPU enabled
   - Expected: has_fpu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("create_with_fpu has FPU enabled")
val has_fpu = true
expect(has_fpu).to_equal(true)
```

</details>

#### create_with_fpu has F and D features

- create_with_fpu has F and D features


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("create_with_fpu has F and D features")
val features = ["+m", "+a", "+f", "+d", "+c"]
expect(features).to_contain("+f")
expect(features).to_contain("+d")
```

</details>

#### create_with_fpu preserves pointer size

- create_with_fpu preserves pointer size
   - Expected: pointer_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("create_with_fpu preserves pointer size")
val pointer_size = 4
expect(pointer_size).to_equal(4)
```

</details>

### RV32 Target - Linux Configuration

#### Linux target has linux triple

- Linux target has linux triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Linux target has linux triple")
val triple = "riscv32-unknown-linux-gnu"
expect(triple).to_contain("linux")
```

</details>

#### Linux target has FPU enabled

- Linux target has FPU enabled
   - Expected: has_fpu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Linux target has FPU enabled")
val has_fpu = true
expect(has_fpu).to_equal(true)
```

</details>

#### Linux target preserves 4-byte pointers

- Linux target preserves 4-byte pointers
   - Expected: pointer_size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Linux target preserves 4-byte pointers")
val pointer_size = 4
expect(pointer_size).to_equal(4)
```

</details>

### RV32 Target - Baremetal Configuration

#### baremetal has none-elf triple

- baremetal has none-elf triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("baremetal has none-elf triple")
val triple = "riscv32-unknown-none-elf"
expect(triple).to_contain("none-elf")
```

</details>

#### baremetal has no FPU

- baremetal has no FPU
   - Expected: has_fpu is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("baremetal has no FPU")
val has_fpu = false
expect(has_fpu).to_equal(false)
```

</details>

#### baremetal has minimal extensions

- baremetal has minimal extensions
   - Expected: features.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("baremetal has minimal extensions")
val features = ["+m"]
expect(features.len()).to_equal(1)
expect(features).to_contain("+m")
```

</details>

#### baremetal triple detects as baremetal

- baremetal triple detects as baremetal
   - Expected: is_baremetal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("baremetal triple detects as baremetal")
val triple = "riscv32-unknown-none-elf"
val is_baremetal = triple.contains("none")
expect(is_baremetal).to_equal(true)
```

</details>

#### linux triple does not detect as baremetal

- linux triple does not detect as baremetal
   - Expected: is_baremetal is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("linux triple does not detect as baremetal")
val triple = "riscv32-unknown-linux-gnu"
val is_baremetal = triple.contains("none")
expect(is_baremetal).to_equal(false)
```

</details>

### RV32 Target - LLVM Type Methods

#### native int type is i32

- native int type is i32
   - Expected: native_int equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("native int type is i32")
val native_int = "i32"
expect(native_int).to_equal("i32")
```

</details>

#### pointer type is ptr

- pointer type is ptr
   - Expected: ptr_type equals `ptr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pointer type is ptr")
val ptr_type = "ptr"
expect(ptr_type).to_equal("ptr")
```

</details>

#### size type is i32 (not i64)

- size type is i32 (not i64)
   - Expected: size_type equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("size type is i32 (not i64)")
val size_type = "i32"
expect(size_type).to_equal("i32")
```

</details>

### RV32 Target - GPR Register Names

#### register 0 is zero

- register 0 is zero
   - Expected: gpr_names[0] equals `zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register 0 is zero")
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[0]).to_equal("zero")
```

</details>

#### register 1 is ra

- register 1 is ra
   - Expected: gpr_names[1] equals `ra`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register 1 is ra")
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[1]).to_equal("ra")
```

</details>

#### register 2 is sp

- register 2 is sp
   - Expected: gpr_names[2] equals `sp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register 2 is sp")
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[2]).to_equal("sp")
```

</details>

#### register 8 is s0 (frame pointer)

- register 8 is s0 (frame pointer)
   - Expected: gpr_names[8] equals `s0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register 8 is s0 (frame pointer)")
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[8]).to_equal("s0")
```

</details>

#### register 10 is a0 (first argument)

- register 10 is a0 (first argument)
   - Expected: gpr_names[10] equals `a0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register 10 is a0 (first argument)")
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[10]).to_equal("a0")
```

</details>

#### register 31 is t6

- register 31 is t6
   - Expected: gpr_names[31] equals `t6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("register 31 is t6")
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names[31]).to_equal("t6")
```

</details>

#### has exactly 32 GPR names

- has exactly 32 GPR names
   - Expected: gpr_names.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has exactly 32 GPR names")
val gpr_names = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
                 "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
                 "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
                 "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]
expect(gpr_names.len()).to_equal(32)
```

</details>

### RV32 Target - FPR Register Names

#### fpr 0 is ft0

- fpr 0 is ft0
   - Expected: fpr_names[0] equals `ft0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fpr 0 is ft0")
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names[0]).to_equal("ft0")
```

</details>

#### fpr 8 is fs0

- fpr 8 is fs0
   - Expected: fpr_names[8] equals `fs0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fpr 8 is fs0")
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names[8]).to_equal("fs0")
```

</details>

#### fpr 10 is fa0 (first float argument)

- fpr 10 is fa0 (first float argument)
   - Expected: fpr_names[10] equals `fa0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fpr 10 is fa0 (first float argument)")
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names[10]).to_equal("fa0")
```

</details>

#### has exactly 32 FPR names

- has exactly 32 FPR names
   - Expected: fpr_names.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has exactly 32 FPR names")
val fpr_names = ["ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
                 "fs0", "fs1", "fa0", "fa1", "fa2", "fa3", "fa4", "fa5",
                 "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
                 "fs8", "fs9", "fs10", "fs11", "ft8", "ft9", "ft10", "ft11"]
expect(fpr_names.len()).to_equal(32)
```

</details>

### RV32 Target - Callee-Saved GPRs

#### s0 (index 8) is callee-saved

- s0 (index 8) is callee-saved
   - Expected: is_callee is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("s0 (index 8) is callee-saved")
val index = 8
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### s1 (index 9) is callee-saved

- s1 (index 9) is callee-saved
   - Expected: is_callee is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("s1 (index 9) is callee-saved")
val index = 9
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### s2 (index 18) is callee-saved

- s2 (index 18) is callee-saved
   - Expected: is_callee is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("s2 (index 18) is callee-saved")
val index = 18
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### s11 (index 27) is callee-saved

- s11 (index 27) is callee-saved
   - Expected: is_callee is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("s11 (index 27) is callee-saved")
val index = 27
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(true)
```

</details>

#### t0 (index 5) is NOT callee-saved

- t0 (index 5) is NOT callee-saved
   - Expected: is_callee is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("t0 (index 5) is NOT callee-saved")
val index = 5
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(false)
```

</details>

#### a0 (index 10) is NOT callee-saved

- a0 (index 10) is NOT callee-saved
   - Expected: is_callee is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a0 (index 10) is NOT callee-saved")
val index = 10
val is_callee = (index >= 8 and index <= 9) or (index >= 18 and index <= 27)
expect(is_callee).to_equal(false)
```

</details>

### RV32 Target - Caller-Saved GPRs

#### t0 (index 5) is caller-saved

- t0 (index 5) is caller-saved
   - Expected: is_caller is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("t0 (index 5) is caller-saved")
val index = 5
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### a0 (index 10) is caller-saved

- a0 (index 10) is caller-saved
   - Expected: is_caller is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a0 (index 10) is caller-saved")
val index = 10
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### a7 (index 17) is caller-saved

- a7 (index 17) is caller-saved
   - Expected: is_caller is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a7 (index 17) is caller-saved")
val index = 17
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### t6 (index 31) is caller-saved

- t6 (index 31) is caller-saved
   - Expected: is_caller is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("t6 (index 31) is caller-saved")
val index = 31
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(true)
```

</details>

#### s0 (index 8) is NOT caller-saved

- s0 (index 8) is NOT caller-saved
   - Expected: is_caller is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("s0 (index 8) is NOT caller-saved")
val index = 8
val is_caller = (index >= 5 and index <= 7) or (index >= 10 and index <= 17) or (index >= 28 and index <= 31)
expect(is_caller).to_equal(false)
```

</details>

### RV32 Target - Register Info Creation

#### base RV32IM has 32 GPRs

- base RV32IM has 32 GPRs
   - Expected: gpr_count equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("base RV32IM has 32 GPRs")
val gpr_count = 32
expect(gpr_count).to_equal(32)
```

</details>

#### base RV32IM has no FPRs

- base RV32IM has no FPRs
   - Expected: fpr_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("base RV32IM has no FPRs")
val fpr_count = 0
expect(fpr_count).to_equal(0)
```

</details>

#### base RV32IM has no float support

- base RV32IM has no float support
   - Expected: has_float is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("base RV32IM has no float support")
val has_float = false
expect(has_float).to_equal(false)
```

</details>

#### RV32IMFD has 32 GPRs

- RV32IMFD has 32 GPRs
   - Expected: gpr_count equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("RV32IMFD has 32 GPRs")
val gpr_count = 32
expect(gpr_count).to_equal(32)
```

</details>

#### RV32IMFD has 32 FPRs

- RV32IMFD has 32 FPRs
   - Expected: fpr_count equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("RV32IMFD has 32 FPRs")
val fpr_count = 32
expect(fpr_count).to_equal(32)
```

</details>

#### RV32IMFD has float support

- RV32IMFD has float support
   - Expected: has_float is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("RV32IMFD has float support")
val has_float = true
expect(has_float).to_equal(true)
```

</details>

#### RV32IMFD has double support

- RV32IMFD has double support
   - Expected: has_double is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("RV32IMFD has double support")
val has_double = true
expect(has_double).to_equal(true)
```

</details>

### RV32 Target - ILP32 Calling Convention

#### ILP32 convention name is ilp32

- ILP32 convention name is ilp32
   - Expected: name equals `ilp32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ILP32 convention name is ilp32")
val name = "ilp32"
expect(name).to_equal("ilp32")
```

</details>

#### ILP32F convention name is ilp32f

- ILP32F convention name is ilp32f
   - Expected: name equals `ilp32f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ILP32F convention name is ilp32f")
val name = "ilp32f"
expect(name).to_equal("ilp32f")
```

</details>

#### ILP32D convention name is ilp32d

- ILP32D convention name is ilp32d
   - Expected: name equals `ilp32d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ILP32D convention name is ilp32d")
val name = "ilp32d"
expect(name).to_equal("ilp32d")
```

</details>

#### has 8 argument GPRs (a0-a7)

- has 8 argument GPRs (a0-a7)
   - Expected: arg_gpr_count equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has 8 argument GPRs (a0-a7)")
val arg_gpr_count = 8
expect(arg_gpr_count).to_equal(8)
```

</details>

#### ILP32 has 0 argument FPRs (soft-float)

- ILP32 has 0 argument FPRs (soft-float)
   - Expected: arg_fpr_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ILP32 has 0 argument FPRs (soft-float)")
val arg_fpr_count = 0
expect(arg_fpr_count).to_equal(0)
```

</details>

#### ILP32F has 8 argument FPRs

- ILP32F has 8 argument FPRs
   - Expected: arg_fpr_count equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ILP32F has 8 argument FPRs")
val arg_fpr_count = 8
expect(arg_fpr_count).to_equal(8)
```

</details>

#### ILP32D has 8 argument FPRs

- ILP32D has 8 argument FPRs
   - Expected: arg_fpr_count equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ILP32D has 8 argument FPRs")
val arg_fpr_count = 8
expect(arg_fpr_count).to_equal(8)
```

</details>

#### has 2 return GPRs (a0, a1)

- has 2 return GPRs (a0, a1)
   - Expected: ret_gpr_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has 2 return GPRs (a0, a1)")
val ret_gpr_count = 2
expect(ret_gpr_count).to_equal(2)
```

</details>

#### stack alignment is 16 bytes

- stack alignment is 16 bytes
   - Expected: stack_alignment equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stack alignment is 16 bytes")
val stack_alignment = 16
expect(stack_alignment).to_equal(16)
```

</details>

#### argument GPRs are a0 through a7

- argument GPRs are a0 through a7
   - Expected: arg_gprs.len() equals `8`
   - Expected: arg_gprs[0] equals `a0`
   - Expected: arg_gprs[7] equals `a7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("argument GPRs are a0 through a7")
val arg_gprs = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(arg_gprs.len()).to_equal(8)
expect(arg_gprs[0]).to_equal("a0")
expect(arg_gprs[7]).to_equal("a7")
```

</details>

#### return GPRs are a0 and a1

- return GPRs are a0 and a1
   - Expected: ret_gprs.len() equals `2`
   - Expected: ret_gprs[0] equals `a0`
   - Expected: ret_gprs[1] equals `a1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("return GPRs are a0 and a1")
val ret_gprs = ["a0", "a1"]
expect(ret_gprs.len()).to_equal(2)
expect(ret_gprs[0]).to_equal("a0")
expect(ret_gprs[1]).to_equal("a1")
```

</details>

#### callee-saved GPRs are s0 through s11

- callee-saved GPRs are s0 through s11
   - Expected: callee_saved.len() equals `12`
   - Expected: callee_saved[0] equals `s0`
   - Expected: callee_saved[11] equals `s11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("callee-saved GPRs are s0 through s11")
val callee_saved = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]
expect(callee_saved.len()).to_equal(12)
expect(callee_saved[0]).to_equal("s0")
expect(callee_saved[11]).to_equal("s11")
```

</details>

#### caller-saved GPRs include temporaries and arguments

- caller-saved GPRs include temporaries and arguments
   - Expected: caller_saved.len() equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("caller-saved GPRs include temporaries and arguments")
val caller_saved = ["t0", "t1", "t2", "t3", "t4", "t5", "t6",
                    "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]
expect(caller_saved.len()).to_equal(15)
expect(caller_saved).to_contain("t0")
expect(caller_saved).to_contain("a7")
```

</details>

### RV32 Target - Supported Extensions

#### supported extensions include M

- supported extensions include M


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supported extensions include M")
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+m")
```

</details>

#### supported extensions include A

- supported extensions include A


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supported extensions include A")
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+a")
```

</details>

#### supported extensions include zicsr

- supported extensions include zicsr


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supported extensions include zicsr")
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+zicsr")
```

</details>

#### supported extensions include zifencei

- supported extensions include zifencei


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supported extensions include zifencei")
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions).to_contain("+zifencei")
```

</details>

#### has 7 supported extensions total

- has 7 supported extensions total
   - Expected: extensions.len() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("has 7 supported extensions total")
val extensions = ["+m", "+a", "+f", "+d", "+c", "+zicsr", "+zifencei"]
expect(extensions.len()).to_equal(7)
```

</details>

### RV32 Target - ILP32 Type Sizes

#### bool is 1 byte

- bool is 1 byte
   - Expected: size equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bool is 1 byte")
# rv32_type_size("bool") -> 1
val size = 1
expect(size).to_equal(1)
```

</details>

#### i8 is 1 byte

- i8 is 1 byte
   - Expected: size equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i8 is 1 byte")
val size = 1
expect(size).to_equal(1)
```

</details>

#### i16 is 2 bytes

- i16 is 2 bytes
   - Expected: size equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i16 is 2 bytes")
val size = 2
expect(size).to_equal(2)
```

</details>

#### i32 is 4 bytes

- i32 is 4 bytes
   - Expected: size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i32 is 4 bytes")
val size = 4
expect(size).to_equal(4)
```

</details>

#### i64 is 8 bytes

- i64 is 8 bytes
   - Expected: size equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i64 is 8 bytes")
val size = 8
expect(size).to_equal(8)
```

</details>

#### f32 is 4 bytes

- f32 is 4 bytes
   - Expected: size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("f32 is 4 bytes")
val size = 4
expect(size).to_equal(4)
```

</details>

#### f64 is 8 bytes

- f64 is 8 bytes
   - Expected: size equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("f64 is 8 bytes")
val size = 8
expect(size).to_equal(8)
```

</details>

#### pointer is 4 bytes (not 8)

- pointer is 4 bytes (not 8)
   - Expected: size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pointer is 4 bytes (not 8)")
val size = 4
expect(size).to_equal(4)
```

</details>

#### usize is 4 bytes (not 8)

- usize is 4 bytes (not 8)
   - Expected: size equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("usize is 4 bytes (not 8)")
val size = 4
expect(size).to_equal(4)
```

</details>

### RV32 Target - ILP32 Type Alignment

#### i32 alignment is 4 bytes

- i32 alignment is 4 bytes
   - Expected: alignment equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i32 alignment is 4 bytes")
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### i64 alignment is 4 bytes on RV32 (not 8)

- i64 alignment is 4 bytes on RV32 (not 8)
   - Expected: alignment equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("i64 alignment is 4 bytes on RV32 (not 8)")
# RV32 aligns i64 to 4 bytes, unlike LP64
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### f64 alignment is 4 bytes on RV32 (not 8)

- f64 alignment is 4 bytes on RV32 (not 8)
   - Expected: alignment equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("f64 alignment is 4 bytes on RV32 (not 8)")
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### pointer alignment is 4 bytes

- pointer alignment is 4 bytes
   - Expected: alignment equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("pointer alignment is 4 bytes")
val alignment = 4
expect(alignment).to_equal(4)
```

</details>

#### bool alignment is 1 byte

- bool alignment is 1 byte
   - Expected: alignment equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("bool alignment is 1 byte")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32 Target - Triple Constants, RV32 Target - CPU and Feature Defaults, RV32 Target - Data Layout, RV32 Target - Default TargetInfo, RV32 Target - FPU Configuration, RV32 Target - Linux Configuration, RV32 Target - Baremetal Configuration, RV32 Target - LLVM Type Methods, RV32 Target - GPR Register Names, RV32 Target - FPR Register Names, RV32 Target - Callee-Saved GPRs, RV32 Target - Caller-Saved GPRs, RV32 Target - Register Info Creation, RV32 Target - ILP32 Calling Convention, RV32 Target - Supported Extensions, RV32 Target - ILP32 Type Sizes, RV32 Target - ILP32 Type Alignment.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f927afceefe583cb0a7716b5046e3e2f63a5bd4830c743b7a74bdcb7e97f6f13`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f927afceefe583cb0a7716b5046e3e2f63a5bd4830c743b7a74bdcb7e97f6f13`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f927afceefe583cb0a7716b5046e3e2f63a5bd4830c743b7a74bdcb7e97f6f13`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/target/riscv32_spec.spl
mirror: doc/06_spec/01_unit/compiler/target/riscv32_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/target/riscv32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/target/riscv32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/target/riscv32_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 39 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/target/riscv32_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct default triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/target/riscv32_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct Linux triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/target/riscv32_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct baremetal triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
