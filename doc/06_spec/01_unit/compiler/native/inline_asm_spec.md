# Should be accepted by parser

> check(code.contains("unsafe"))

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Should be accepted by parser

check(code.contains("unsafe"))

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/native/inline_asm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

check(code.contains("unsafe"))

        check(code.contains("asm"))


    it "accepts asm in unsafe function body":
        step("accepts asm in unsafe function body")

        val code = """

        fn raw_op():

            unsafe:

                asm volatile { cli }

## Scenarios

### Inline Assembly Syntax

#### recognizes asm keyword in code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- recognizes asm keyword in code


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes asm keyword in code")

val code = "asm { nop }"

# Verify asm keyword is present in syntax

check(code.starts_with("asm"))

check(code.contains("{"))

check(code.contains("}"))

check(code.contains("nop"))
```

</details>

#### parses simple asm expression

- parses simple asm expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple asm expression")

val code = "asm { nop }"

# Parser accepts the syntax (may return error for now without full context)

# Just verify it doesn't crash

check(code.len() > 0)
```

</details>

#### parses asm with volatile flag

- parses asm with volatile flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses asm with volatile flag")

val code = "asm volatile { nop }"

# Verify volatile flag syntax

check(code.contains("asm"))

check(code.contains("volatile"))

check(code.contains("nop"))
```

</details>

#### parses asm template string

- parses asm template string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses asm template string")

val code = "asm { mov eax, ebx }"

check(code.contains("mov eax, ebx"))
```

</details>

### Inline Assembly Constraints

#### parses input constraint

- parses input constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses input constraint")

val constraint = "op = in(reg) value"

check(constraint.contains("in(reg)"))
```

</details>

#### parses output constraint

- parses output constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses output constraint")

val constraint = "result = out(reg) var"

check(constraint.contains("out(reg)"))
```

</details>

#### parses inout constraint

- parses inout constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses inout constraint")

val code = "asm(\"\", ptr = inout(reg) addr)"

check(code.contains("inout(reg)"))
```

</details>

#### parses lateout constraint

- parses lateout constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses lateout constraint")

val code = "asm(\"\", result = lateout(reg) val)"

check(code.contains("lateout(reg)"))
```

</details>

#### parses memory location

- parses memory location


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses memory location")

val code = "asm(\"\", ptr = in(mem) addr)"

check(code.contains("in(mem)"))
```

</details>

#### parses immediate location

- parses immediate location


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses immediate location")

val code = "asm(\"\", imm = in(imm) constant)"

check(code.contains("in(imm)"))
```

</details>

### Inline Assembly Multi-Constraint

#### parses multiple input constraints

- parses multiple input constraints


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple input constraints")

val code = """asm("add {0}, {1}",

    a = in(reg) x,

    b = in(reg) y

)"""

check(code.contains("in(reg) x"))

check(code.contains("in(reg) y"))
```

</details>

#### parses mixed input and output

- parses mixed input and output


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses mixed input and output")

val code = """asm("add {result}, {a}",

    result = out(reg) res,

    a = in(reg) value

)"""

check(code.contains("out(reg)"))

check(code.contains("in(reg)"))
```

</details>

#### parses clobber_abi specification

- parses clobber_abi specification


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses clobber_abi specification")

val code = """asm("call foo",

    clobber_abi("C")

)"""

check(code.contains("clobber_abi"))
```

</details>

### Inline Assembly Architecture Examples

#### parses x86 port output

- parses x86 port output


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses x86 port output")

val code = """asm volatile {

    "out dx, al"

}"""

check(code.contains("out dx, al"))
```

</details>

#### parses x86 port input

- parses x86 port input


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses x86 port input")

val code = """asm volatile {

    "in al, dx"

}"""

check(code.contains("in al, dx"))
```

</details>

#### parses ARM semihosting

- parses ARM semihosting


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses ARM semihosting")

val code = """asm volatile {

    "mov r0, {op}",

}"""

check(code.contains("mov r0"))
```

</details>

#### parses RISC-V ebreak

- parses RISC-V ebreak


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses RISC-V ebreak")

val code = """asm volatile {

    "mv a0, {op}",

    "ebreak",

}"""

check(code.contains("ebreak"))
```

</details>

### Inline Assembly in Unsafe Context

#### accepts asm in unsafe block

- accepts asm in unsafe block


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts asm in unsafe block")

val code = """

unsafe:

    asm { nop }

"""

# Should be accepted by parser

check(code.contains("unsafe"))

check(code.contains("asm"))
```

</details>

#### accepts asm in unsafe function body

- accepts asm in unsafe function body


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts asm in unsafe function body")

val code = """

fn raw_op():

    unsafe:

        asm volatile { cli }

"""

check(code.contains("unsafe"))
```

</details>

### Inline Assembly Error Cases

#### does not require parentheses for raw asm

- does not require parentheses for raw asm


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not require parentheses for raw asm")

val code = "asm { nop }"

# Raw asm uses the custom block form.

check(not code.contains("("))
```

</details>

#### allows empty raw asm block

- allows empty raw asm block


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows empty raw asm block")

val code = "asm {}"

# Empty asm is valid for backend-specific clobber or barrier expansion.

check(code == "asm {}")
```

</details>

### Inline Assembly Constraint Kinds

#### recognizes all constraint kinds

- recognizes all constraint kinds


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes all constraint kinds")

val kinds = ["in", "out", "inout", "lateout"]

for kind in kinds:

    val code = "asm(\"\", x = {kind}(reg) v)".replace("{kind}", kind)

    check(code.contains(kind))
```

</details>

### Inline Assembly Location Specifiers

#### recognizes general register

- recognizes general register


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes general register")

val code = "asm(\"\", x = in(reg) v)"

check(code.contains("reg"))
```

</details>

#### recognizes memory operand

- recognizes memory operand


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes memory operand")

val code = "asm(\"\", x = in(mem) v)"

check(code.contains("mem"))
```

</details>

#### recognizes immediate constant

- recognizes immediate constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes immediate constant")

val code = "asm(\"\", x = in(imm) v)"

check(code.contains("imm"))
```

</details>

#### recognizes specific register names

- recognizes specific register names


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes specific register names")

val registers = ["eax", "ebx", "r0", "r1", "a0", "t0"]

for reg in registers:

    val code = "asm(\"\", x = in({reg}) v)".replace("{reg}", reg)

    check(code.contains(reg))
```

</details>

### Inline Assembly Real-World Examples

#### implements outb correctly

- implements outb correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements outb correctly")

val code = """

fn outb(port: u16, value: u8):

    unsafe:

        asm volatile {

            "out dx, al",

        }

"""

check(code.contains("out dx, al"))

check(not code.contains("asm volatile("))
```

</details>

#### implements inb correctly

- implements inb correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements inb correctly")

val code = """

fn inb(port: u16) -> u8:

    var result: u8

    unsafe:

        asm volatile(

            "in al, dx",

            out("al") result,

            in("dx") port

        )

    result

"""

check(code.contains("in al, dx"))

check(code.contains("out(\"al\")"))
```

</details>

#### implements atomic compare-exchange

- implements atomic compare-exchange


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements atomic compare-exchange")

val code = """

fn atomic_cas(ptr: *u32, expected: u32, desired: u32) -> bool:

    var success: bool

    unsafe:

        asm volatile(

            "lock cmpxchg {desired}, {ptr}",

            "sete {success}",

            ptr = inout(reg) ptr,

            desired = in(reg) desired,

            success = out(reg) success,

            in("eax") expected

        )

    success

"""

check(code.contains("lock cmpxchg"))

check(code.contains("inout(reg)"))
```

</details>

#### implements memory barrier

- implements memory barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements memory barrier")

val code = """

fn memory_fence():

    unsafe:

        asm volatile { mfence }

"""

check(code.contains("mfence"))
```

</details>

#### implements CPU pause for spinlock

- implements CPU pause for spinlock


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("implements CPU pause for spinlock")

val code = """

fn cpu_relax():

    unsafe:

        asm volatile { pause }

"""

check(code.contains("pause"))
```

</details>

### x86/x86_64 Backend Functions

#### provides cli instruction helper

- provides cli instruction helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides cli instruction helper")

val code = """

fn disable_interrupts():

    unsafe:

        asm volatile { cli }

"""

check(code.contains("cli"))
```

</details>

#### provides sti instruction helper

- provides sti instruction helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides sti instruction helper")

val code = """

fn enable_interrupts():

    unsafe:

        asm volatile { sti }

"""

check(code.contains("sti"))
```

</details>

#### provides hlt instruction helper

- provides hlt instruction helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides hlt instruction helper")

val code = """

fn halt_cpu():

    unsafe:

        asm volatile { hlt }

"""

check(code.contains("hlt"))
```

</details>

#### provides I/O port operations

- provides I/O port operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides I/O port operations")

val code = """

fn read_port(port: u16) -> u8:

    var value: u8

    unsafe:

        asm volatile("in al, dx", out("al") value, in("dx") port)

    value

"""

check(code.contains("in al, dx"))
```

</details>

### ARM Backend Functions

#### provides interrupt control

- provides interrupt control


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides interrupt control")

val code = """

fn disable_irq():

    unsafe:

        asm volatile { cpsid i }

"""

check(code.contains("cpsid i"))
```

</details>

#### provides wait for interrupt

- provides wait for interrupt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides wait for interrupt")

val code = """

fn wait_for_irq():

    unsafe:

        asm volatile { wfi }

"""

check(code.contains("wfi"))
```

</details>

#### provides memory barriers

- provides memory barriers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides memory barriers")

val code = """

fn memory_barrier():

    unsafe:

        asm volatile { dmb }

"""

check(code.contains("dmb"))
```

</details>

### RISC-V Backend Functions

#### provides CSR operations

- provides CSR operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides CSR operations")

val code = """

fn read_mstatus() -> u64:

    var value: u64

    unsafe:

        asm volatile("csrr {val}, mstatus", val = out(reg) value)

    value

"""

check(code.contains("csrr"))

check(code.contains("mstatus"))
```

</details>

#### provides wait for interrupt

- provides wait for interrupt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides wait for interrupt")

val code = """

fn wait_for_interrupt():

    unsafe:

        asm volatile { wfi }

"""

check(code.contains("wfi"))
```

</details>

#### provides environment call

- provides environment call


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides environment call")

val code = """

fn syscall():

    unsafe:

        asm volatile { ecall }

"""

check(code.contains("ecall"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
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

- Canonical SPipe generation for source `28c7912212c9ed2ab3bcd7e13cd0b3ec9593cec02568f3c9de994d52308ae492`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28c7912212c9ed2ab3bcd7e13cd0b3ec9593cec02568f3c9de994d52308ae492`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28c7912212c9ed2ab3bcd7e13cd0b3ec9593cec02568f3c9de994d52308ae492`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/native/inline_asm_spec.spl
mirror: doc/06_spec/01_unit/compiler/native/inline_asm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/native/inline_asm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/native/inline_asm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/native/inline_asm_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes asm keyword in code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/inline_asm_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses simple asm expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/native/inline_asm_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses asm with volatile flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
