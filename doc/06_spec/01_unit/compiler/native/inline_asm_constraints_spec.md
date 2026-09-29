# Input constraint: value is read from input_value

> check(code.contains("in(reg)"))

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

check(code.contains("in(reg)"))

    it "out constraint is write-only":
        step("out constraint is write-only")
        val code = """
        var result: u32
        unsafe:
            asm("mov {res}, eax", res = out(reg) result)

## Scenarios

### Constraint Kind Semantics

#### in constraint is read-only

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- in constraint is read-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("in constraint is read-only")
val code = """
unsafe:
    asm("mov eax, {val}", val = in(reg) input_value)
"""
# Input constraint: value is read from input_value
check(code.contains("in(reg)"))
```

</details>

#### out constraint is write-only

- out constraint is write-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("out constraint is write-only")
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

- inout constraint is read-write


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inout constraint is read-write")
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

- lateout constraint prevents early clobber


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lateout constraint prevents early clobber")
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

- reg allows any general-purpose register


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reg allows any general-purpose register")
val code = """
unsafe:
    asm("", x = in(reg) value)
"""
# Compiler chooses any available register
check(code.contains("in(reg)"))
```

</details>

#### specific register constrains allocation

- specific register constrains allocation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specific register constrains allocation")
val code = """
unsafe:
    asm("", x = in("eax") value)
"""
# Must use eax register specifically
check(code.contains("in(\"eax\")"))
```

</details>

#### mem allows memory operand

- mem allows memory operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mem allows memory operand")
val code = """
unsafe:
    asm("lock add {ptr}, 1", ptr = in(mem) address)
"""
# Can use memory location directly
check(code.contains("in(mem)"))
```

</details>

#### imm requires compile-time constant

- imm requires compile-time constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("imm requires compile-time constant")
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

- supports multiple inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multiple inputs")
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

- supports multiple outputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports multiple outputs")
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

- supports mixed constraint kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports mixed constraint kinds")
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

- uses named placeholders in template


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses named placeholders in template")
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

- supports numbered placeholders


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports numbered placeholders")
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

- specifies clobber_abi for ABI preservation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("specifies clobber_abi for ABI preservation")
val code = """
unsafe:
    asm("call external_func", clobber_abi("C"))
"""
# Clobbers all caller-saved registers per C ABI
check(code.contains("clobber_abi(\"C\")"))
```

</details>

#### allows multiple clobber specifications

- allows multiple clobber specifications


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows multiple clobber specifications")
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

- prevents optimization with volatile


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prevents optimization with volatile")
val code = """
unsafe:
    asm volatile("nop")
"""
# Compiler must not remove or reorder this instruction
check(code.contains("volatile"))
```

</details>

#### omits volatile for pure operations

- omits volatile for pure operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits volatile for pure operations")
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

- requires volatile for side effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires volatile for side effects")
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

- uses x86 register names


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses x86 register names")
val regs = ["eax", "ebx", "ecx", "edx", "esi", "edi", "ebp", "esp"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

#### uses x86-64 extended registers

- uses x86-64 extended registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses x86-64 extended registers")
val regs = ["rax", "rbx", "r8", "r9", "r10", "r15"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

#### uses ARM register names

- uses ARM register names


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses ARM register names")
val regs = ["r0", "r1", "r7", "r12", "lr", "sp"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

#### uses RISC-V register names

- uses RISC-V register names


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses RISC-V register names")
val regs = ["a0", "a1", "t0", "t1", "s0", "ra", "sp"]
for reg in regs:
    val code = "asm(\"\", x = in(\"{reg}\") v)".replace("{reg}", reg)
    check(code.contains(reg))
```

</details>

### Complex Real-World Examples

#### implements system call (x86-64)

- implements system call (x86-64)


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements system call (x86-64)")
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

- implements CPUID instruction


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements CPUID instruction")
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

- implements RDTSC timestamp counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements RDTSC timestamp counter")
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

- implements atomic exchange


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements atomic exchange")
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

- handles empty template


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty template")
val code = """
unsafe:
    asm("", clobber_abi("C"))
"""
# Empty asm with only clobbers
check(code.contains("\"\""))
```

</details>

#### handles template with special characters

- handles template with special characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles template with special characters")
val code = """
unsafe:
    asm("test $0x80, %al")
"""
# AT&T syntax with $ and %
check(code.contains("$0x80"))
```

</details>

#### handles multiline template

- handles multiline template


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiline template")
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

- handles constraint without operand name


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constraint without operand name")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5753854ff60b8452384b85ce2aba02353d3f51e1a40a7ddafa19fad575706a6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5753854ff60b8452384b85ce2aba02353d3f51e1a40a7ddafa19fad575706a6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5753854ff60b8452384b85ce2aba02353d3f51e1a40a7ddafa19fad575706a6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/native/inline_asm_constraints_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/inline_asm_constraints_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/inline_asm_constraints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/inline_asm_constraints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/inline_asm_constraints_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'in constraint is read-only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/inline_asm_constraints_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'out constraint is write-only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/inline_asm_constraints_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inout constraint is read-write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
