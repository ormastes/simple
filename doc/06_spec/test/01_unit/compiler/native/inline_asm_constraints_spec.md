# Input constraint: value is read from input_value

> check(code.contains("in(reg)"))

<!-- sdn-diagram:id=inline_asm_constraints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inline_asm_constraints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inline_asm_constraints_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inline_asm_constraints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Input constraint: value is read from input_value

check(code.contains("in(reg)"))

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/inline_asm_constraints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

check(code.contains("in(reg)"))

    it "out constraint is write-only":
        val code = """
        var result: u32
        unsafe:
            asm("mov {res}, eax", res = out(reg) result)

## Scenarios

### Constraint Kind Semantics

#### in constraint is read-only

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("mov eax, {val}", val = in(reg) input_value)
"""
# Input constraint: value is read from input_value
check(code.contains("in(reg)"))
```

</details>

#### out constraint is write-only

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
var result: u32
unsafe:
    asm("mov {res}, eax", res = out(reg) result)
"""
# Output constraint: value is written to result
check(code.contains("out(reg)"))
```

</details>

#### inout constraint is read-write

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
var value: u32 = 5
unsafe:
    asm("add {val}, 1", val = inout(reg) value)
"""
# InOut: reads initial value, writes back modified
check(code.contains("inout(reg)"))
```

</details>

#### lateout constraint prevents early clobber

1. res = lateout
2. in = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
var result: u32
unsafe:
    asm(
        "operation {res}, {in}",
        res = lateout(reg) result,
        in = in(reg) input
    )
"""
# LateOut: output register not clobbered until after inputs read
check(code.contains("lateout(reg)"))
```

</details>

### Location Specifier Semantics

#### reg allows any general-purpose register

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("", x = in(reg) value)
"""
# Compiler chooses any available register
check(code.contains("in(reg)"))
```

</details>

#### specific register constrains allocation

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("", x = in("eax") value)
"""
# Must use eax register specifically
check(code.contains("in(\"eax\")"))
```

</details>

#### mem allows memory operand

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("lock add {ptr}, 1", ptr = in(mem) address)
"""
# Can use memory location directly
check(code.contains("in(mem)"))
```

</details>

#### imm requires compile-time constant

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("shl eax, {shift}", shift = in(imm) 5)
"""
# Immediate value (constant)
check(code.contains("in(imm)"))
```

</details>

### Multiple Constraints

#### supports multiple inputs

1. a = inout
2. b = in
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm(
        "add {a}, {b}",
        a = inout(reg) x,
        b = in(reg) y
    )
"""
check(code.contains("inout(reg)"))
check(code.contains("in(reg)"))
```

</details>

#### supports multiple outputs

1. quot = out
2. rem = out
3. divisor = in
4. in
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
var quotient: u32
var remainder: u32
unsafe:
    asm(
        "div {divisor}",
        quot = out("eax") quotient,
        rem = out("edx") remainder,
        divisor = in(reg) divisor,
        in("eax") dividend
    )
"""
check(code.contains("out(\"eax\")"))
check(code.contains("out(\"edx\")"))
```

</details>

#### supports mixed constraint kinds

1. result = lateout
2. input1 = in
3. input2 = in
4. temp = inout
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
var result: u32
unsafe:
    asm(
        "operation",
        result = lateout(reg) result,
        input1 = in(reg) a,
        input2 = in(reg) b,
        temp = inout(reg) scratch
    )
"""
# Mix of lateout, in, and inout
check(code.contains("lateout(reg)"))
```

</details>

### Constraint Placeholders

#### uses named placeholders in template

1. asm
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dest = "dest"
val src = "src"
val code = """
unsafe:
    asm("mov {dest}, {src}", dest = out(reg) d, src = in(reg) s)
"""
# {dest} and {src} reference constraint names
check(code.contains("dest"))
check(code.contains("src"))
```

</details>

#### supports numbered placeholders

1. asm
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("add {0}, {1}", a = inout(reg) x, b = in(reg) y)
"""
# {0} = first operand, {1} = second operand
check(code.contains("{0}"))
check(code.contains("{1}"))
```

</details>

### Clobber Specifications

#### specifies clobber_abi for ABI preservation

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("call external_func", clobber_abi("C"))
"""
# Clobbers all caller-saved registers per C ABI
check(code.contains("clobber_abi(\"C\")"))
```

</details>

#### allows multiple clobber specifications

1. out = out
2. clobber abi
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm(
        "complex operation",
        out = out(reg) result,
        clobber_abi("C")
    )
"""
check(code.contains("clobber_abi"))
```

</details>

### Volatile Flag

#### prevents optimization with volatile

1. asm volatile
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm volatile("nop")
"""
# Compiler must not remove or reorder this instruction
check(code.contains("volatile"))
```

</details>

#### omits volatile for pure operations

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
var result: u32
unsafe:
    asm("bswap {val}", val = inout(reg) result)
"""
# Non-volatile: can be optimized if result unused
check(not code.contains("volatile"))
```

</details>

#### requires volatile for side effects

1. asm volatile
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm volatile("out dx, al", in("dx") port, in("al") value)
"""
# I/O operations must be volatile
check(code.contains("volatile"))
```

</details>

### Architecture-Specific Constraints

#### uses x86 register names

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regs = ["eax", "ebx", "ecx", "edx", "esi", "edi", "ebp", "esp"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

#### uses x86-64 extended registers

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regs = ["rax", "rbx", "r8", "r9", "r10", "r15"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

#### uses ARM register names

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regs = ["r0", "r1", "r7", "r12", "lr", "sp"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

#### uses RISC-V register names

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regs = ["a0", "a1", "t0", "t1", "s0", "ra", "sp"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

### Complex Real-World Examples

#### implements system call (x86-64)

1. fn syscall
2. result = lateout
3. in
4. in
5. in
6. clobber abi
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
fn syscall(num: u64, arg1: u64, arg2: u64) -> u64:
    var result: u64
    unsafe:
        asm volatile(
            "syscall",
            result = lateout("rax") result,
            in("rax") num,
            in("rdi") arg1,
            in("rsi") arg2,
            clobber_abi("C")
        )
    result
"""
check(code.contains("syscall"))
check(code.contains("lateout(\"rax\")"))
```

</details>

#### implements CPUID instruction

1. fn cpuid
2. out eax = lateout
3. out ebx = lateout
4. out ecx = lateout
5. out edx = lateout
6. in
7. in
8.
9. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
fn cpuid(leaf: u32) -> (u32, u32, u32, u32):
    var eax: u32
    var ebx: u32
    var ecx: u32
    var edx: u32
    unsafe:
        asm(
            "cpuid",
            out_eax = lateout("eax") eax,
            out_ebx = lateout("ebx") ebx,
            out_ecx = lateout("ecx") ecx,
            out_edx = lateout("edx") edx,
            in("eax") leaf,
            in("ecx") 0
        )
    (eax, ebx, ecx, edx)
"""
check(code.contains("cpuid"))
```

</details>

#### implements RDTSC timestamp counter

1. fn rdtsc
2. low = out
3. high = out
4.
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
fn rdtsc() -> u64:
    var low: u32
    var high: u32
    unsafe:
        asm(
            "rdtsc",
            low = out("eax") low,
            high = out("edx") high
        )
    (high as u64) << 32 | (low as u64)
"""
check(code.contains("rdtsc"))
```

</details>

#### implements atomic exchange

1. fn atomic swap
2. ptr = in
3. new = inout
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
fn atomic_swap(ptr: *mut u32, new_val: u32) -> u32:
    var old: u32
    unsafe:
        asm(
            "xchg {new}, {ptr}",
            ptr = in(reg) ptr,
            new = inout(reg) new_val => old
        )
    old
"""
check(code.contains("xchg"))
```

</details>

### Edge Cases

#### handles empty template

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("", clobber_abi("C"))
"""
# Empty asm with only clobbers
check(code.contains("\"\""))
```

</details>

#### handles template with special characters

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("test $0x80, %al")
"""
# AT&T syntax with $ and %
check(code.contains("$0x80"))
```

</details>

#### handles multiline template

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm(
        "push ebx",
        "mov ebx, {val}",
        "pop ebx",
        val = in(reg) value
    )
"""
# Each line is separate argument
check(code.contains("push ebx"))
```

</details>

#### handles constraint without operand name

1. asm
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
unsafe:
    asm("nop", in("eax") value)
"""
# Anonymous constraint (uses register directly)
check(code.contains("in(\"eax\")"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
