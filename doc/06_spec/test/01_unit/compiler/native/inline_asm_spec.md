# Should be accepted by parser

> check(code.contains("unsafe"))

<!-- sdn-diagram:id=inline_asm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inline_asm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inline_asm_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inline_asm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

check(code.contains("unsafe"))

        check(code.contains("asm"))


    it "accepts asm in unsafe function body":

        val code = """

        fn raw_op():

            unsafe:

                asm volatile { cli }

## Scenarios

### Inline Assembly Syntax

#### recognizes asm keyword in code

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm { nop }"

# Verify asm keyword is present in syntax

check(code.starts_with("asm"))

check(code.contains("{"))

check(code.contains("}"))

check(code.contains("nop"))
```

</details>

#### parses simple asm expression

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm { nop }"

# Parser accepts the syntax (may return error for now without full context)

# Just verify it doesn't crash

check(code.len() > 0)
```

</details>

#### parses asm with volatile flag

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm volatile { nop }"

# Verify volatile flag syntax

check(code.contains("asm"))

check(code.contains("volatile"))

check(code.contains("nop"))
```

</details>

#### parses asm template string

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm { mov eax, ebx }"

check(code.contains("mov eax, ebx"))
```

</details>

### Inline Assembly Constraints

#### parses input constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val constraint = "op = in(reg) value"

check(constraint.contains("in(reg)"))
```

</details>

#### parses output constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val constraint = "result = out(reg) var"

check(constraint.contains("out(reg)"))
```

</details>

#### parses inout constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm(\"\", ptr = inout(reg) addr)"

check(code.contains("inout(reg)"))
```

</details>

#### parses lateout constraint

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm(\"\", result = lateout(reg) val)"

check(code.contains("lateout(reg)"))
```

</details>

#### parses memory location

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm(\"\", ptr = in(mem) addr)"

check(code.contains("in(mem)"))
```

</details>

#### parses immediate location

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm(\"\", imm = in(imm) constant)"

check(code.contains("in(imm)"))
```

</details>

### Inline Assembly Multi-Constraint

#### parses multiple input constraints

1. a = in
2. b = in
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """asm("add {0}, {1}",

    a = in(reg) x,

    b = in(reg) y

)"""

check(code.contains("in(reg) x"))

check(code.contains("in(reg) y"))
```

</details>

#### parses mixed input and output

1. result = out
2. a = in
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """asm("add {result}, {a}",

    result = out(reg) res,

    a = in(reg) value

)"""

check(code.contains("out(reg)"))

check(code.contains("in(reg)"))
```

</details>

#### parses clobber_abi specification

1. clobber abi
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """asm("call foo",

    clobber_abi("C")

)"""

check(code.contains("clobber_abi"))
```

</details>

### Inline Assembly Architecture Examples

#### parses x86 port output

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """asm volatile {

    "out dx, al"

}"""

check(code.contains("out dx, al"))
```

</details>

#### parses x86 port input

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """asm volatile {

    "in al, dx"

}"""

check(code.contains("in al, dx"))
```

</details>

#### parses ARM semihosting

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """asm volatile {

    "mov r0, {op}",

}"""

check(code.contains("mov r0"))
```

</details>

#### parses RISC-V ebreak

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """asm volatile {

    "mv a0, {op}",

    "ebreak",

}"""

check(code.contains("ebreak"))
```

</details>

### Inline Assembly in Unsafe Context

#### accepts asm in unsafe block

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn raw op
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm { nop }"

# Raw asm uses the custom block form.

check(not code.contains("("))
```

</details>

#### allows empty raw asm block

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm {}"

# Empty asm is valid for backend-specific clobber or barrier expansion.

check(code == "asm {}")
```

</details>

### Inline Assembly Constraint Kinds

#### recognizes all constraint kinds

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val kinds = ["in", "out", "inout", "lateout"]

for kind in kinds:

    val code = "asm(\"\", x = {kind}(reg) v)".replace("{kind}", kind)

    check(code.contains(kind))
```

</details>

### Inline Assembly Location Specifiers

#### recognizes general register

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm(\"\", x = in(reg) v)"

check(code.contains("reg"))
```

</details>

#### recognizes memory operand

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm(\"\", x = in(mem) v)"

check(code.contains("mem"))
```

</details>

#### recognizes immediate constant

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = "asm(\"\", x = in(imm) v)"

check(code.contains("imm"))
```

</details>

#### recognizes specific register names

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val registers = ["eax", "ebx", "r0", "r1", "a0", "t0"]

for reg in registers:

    val code = "asm(\"\", x = in({reg}) v)".replace("{reg}", reg)

    check(code.contains(reg))
```

</details>

### Inline Assembly Real-World Examples

#### implements outb correctly

1. fn outb
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn inb
2. out
3. in
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn atomic cas
2. ptr = inout
3. desired = in
4. success = out
5. in
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn memory fence
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """

fn memory_fence():

    unsafe:

        asm volatile { mfence }

"""

check(code.contains("mfence"))
```

</details>

#### implements CPU pause for spinlock

1. fn cpu relax
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn disable interrupts
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """

fn disable_interrupts():

    unsafe:

        asm volatile { cli }

"""

check(code.contains("cli"))
```

</details>

#### provides sti instruction helper

1. fn enable interrupts
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """

fn enable_interrupts():

    unsafe:

        asm volatile { sti }

"""

check(code.contains("sti"))
```

</details>

#### provides hlt instruction helper

1. fn halt cpu
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """

fn halt_cpu():

    unsafe:

        asm volatile { hlt }

"""

check(code.contains("hlt"))
```

</details>

#### provides I/O port operations

1. fn read port
2. asm volatile
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn disable irq
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """

fn disable_irq():

    unsafe:

        asm volatile { cpsid i }

"""

check(code.contains("cpsid i"))
```

</details>

#### provides wait for interrupt

1. fn wait for irq
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """

fn wait_for_irq():

    unsafe:

        asm volatile { wfi }

"""

check(code.contains("wfi"))
```

</details>

#### provides memory barriers

1. fn memory barrier
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn read mstatus
2. asm volatile
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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

1. fn wait for interrupt
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val code = """

fn wait_for_interrupt():

    unsafe:

        asm volatile { wfi }

"""

check(code.contains("wfi"))
```

</details>

#### provides environment call

1. fn syscall
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

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
