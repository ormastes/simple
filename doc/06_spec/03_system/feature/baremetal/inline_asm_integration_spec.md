# Inline Assembly Integration

> Tests inline assembly integration with the Simple compiler including register constraints, clobber lists, and memory operands. Verifies that inline asm blocks are correctly emitted and that the compiler respects assembly side effects.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Assembly Integration

Tests inline assembly integration with the Simple compiler including register constraints, clobber lists, and memory operands. Verifies that inline asm blocks are correctly emitted and that the compiler respects assembly side effects.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/inline_asm_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests inline assembly integration with the Simple compiler including register
constraints, clobber lists, and memory operands. Verifies that inline asm blocks
are correctly emitted and that the compiler respects assembly side effects.

## Scenarios

### x86 Port I/O Operations

<details>
<summary>Advanced: implements outb for serial port</summary>

#### implements outb for serial port _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- implements outb for serial port


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements outb for serial port")
val code = """
fn serial_write_byte(byte: u8):
    val COM1_PORT: u16 = 0x3F8
    unsafe:
        asm volatile(
            "out dx, al",
            in("dx") COM1_PORT,
            in("al") byte
        )
"""
check(code.contains("out dx, al"))
check(code.contains("COM1_PORT"))
```

</details>


</details>

<details>
<summary>Advanced: implements inb for serial port status</summary>

#### implements inb for serial port status _(slow)_

- implements inb for serial port status


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements inb for serial port status")
val code = """
fn serial_can_write() -> bool:
    val COM1_STATUS: u16 = 0x3FD
    var status: u8
    unsafe:
        asm volatile(
            "in al, dx",
            out("al") status,
            in("dx") COM1_STATUS
        )
    (status & 0x20) != 0
"""
check(code.contains("in al, dx"))
```

</details>


</details>

<details>
<summary>Advanced: implements outw for 16-bit I/O</summary>

#### implements outw for 16-bit I/O _(slow)_

- implements outw for 16-bit I/O


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements outw for 16-bit I/O")
val code = """
fn pci_write_config(addr: u32, value: u16):
    unsafe:
        # Write address to config address port
        asm volatile(
            "out dx, eax",
            in("dx") 0xCF8 as u16,
            in("eax") addr
        )
        # Write data to config data port
        asm volatile(
            "out dx, ax",
            in("dx") 0xCFC as u16,
            in("ax") value
        )
"""
check(code.contains("out dx, eax"))
check(code.contains("out dx, ax"))
```

</details>


</details>

### x86 CPU Control

<details>
<summary>Advanced: implements CLI to disable interrupts</summary>

#### implements CLI to disable interrupts _(slow)_

- implements CLI to disable interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements CLI to disable interrupts")
val code = """
fn disable_interrupts():
    unsafe:
        asm volatile { cli }
"""
check(code.contains("cli"))
```

</details>


</details>

<details>
<summary>Advanced: implements STI to enable interrupts</summary>

#### implements STI to enable interrupts _(slow)_

- implements STI to enable interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements STI to enable interrupts")
val code = """
fn enable_interrupts():
    unsafe:
        asm volatile { sti }
"""
check(code.contains("sti"))
```

</details>


</details>

<details>
<summary>Advanced: implements HLT to halt CPU</summary>

#### implements HLT to halt CPU _(slow)_

- implements HLT to halt CPU


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements HLT to halt CPU")
val code = """
fn halt():
    unsafe:
        asm volatile { hlt }
"""
check(code.contains("hlt"))
```

</details>


</details>

<details>
<summary>Advanced: implements LGDT to load GDT</summary>

#### implements LGDT to load GDT _(slow)_

- implements LGDT to load GDT


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements LGDT to load GDT")
val code = """
fn load_gdt(gdt_ptr: u64):
    unsafe:
        asm volatile(
            "lgdt [{ptr}]",
            ptr = in(reg) gdt_ptr
        )
"""
check(code.contains("lgdt"))
```

</details>


</details>

<details>
<summary>Advanced: implements LIDT to load IDT</summary>

#### implements LIDT to load IDT _(slow)_

- implements LIDT to load IDT


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements LIDT to load IDT")
val code = """
fn load_idt(idt_ptr: u64):
    unsafe:
        asm volatile(
            "lidt [{ptr}]",
            ptr = in(reg) idt_ptr
        )
"""
check(code.contains("lidt"))
```

</details>


</details>

### x86 Control Registers

<details>
<summary>Advanced: reads CR0 control register</summary>

#### reads CR0 control register _(slow)_

- reads CR0 control register


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads CR0 control register")
val code = """
fn read_cr0() -> u32:
    var value: u32
    unsafe:
        asm(
            "mov {val}, cr0",
            val = out(reg) value
        )
    value
"""
check(code.contains("mov"))
check(code.contains("cr0"))
```

</details>


</details>

<details>
<summary>Advanced: writes CR3 page directory</summary>

#### writes CR3 page directory _(slow)_

- writes CR3 page directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes CR3 page directory")
val code = """
fn load_page_directory(addr: u32):
    unsafe:
        asm volatile(
            "mov cr3, {addr}",
            addr = in(reg) addr
        )
"""
check(code.contains("cr3"))
```

</details>


</details>

### ARM Bare-Metal Operations

<details>
<summary>Advanced: implements ARM semihosting call</summary>

#### implements ARM semihosting call _(slow)_

- implements ARM semihosting call


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements ARM semihosting call")
val code = """
fn arm_semihost(op: u32, params: u64) -> i64:
    var result: i64
    unsafe:
        asm volatile(
            "mov r0, {op}",
            "mov r1, {params}",
            "bkpt #0xAB",
            "mov {result}, r0",
            op = in(reg) op,
            params = in(reg) params,
            result = lateout(reg) result,
            clobber_abi("C")
        )
    result
"""
check(code.contains("bkpt #0xAB"))
check(code.contains("mov r0"))
```

</details>


</details>

<details>
<summary>Advanced: implements ARM WFI (wait for interrupt)</summary>

#### implements ARM WFI (wait for interrupt) _(slow)_

- implements ARM WFI (wait for interrupt)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements ARM WFI (wait for interrupt)")
val code = """
fn wait_for_interrupt():
    unsafe:
        asm volatile { wfi }
"""
check(code.contains("wfi"))
```

</details>


</details>

<details>
<summary>Advanced: implements ARM data barrier</summary>

#### implements ARM data barrier _(slow)_

- implements ARM data barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements ARM data barrier")
val code = """
fn data_memory_barrier():
    unsafe:
        asm volatile { dmb }
"""
check(code.contains("dmb"))
```

</details>


</details>

<details>
<summary>Advanced: implements ARM instruction barrier</summary>

#### implements ARM instruction barrier _(slow)_

- implements ARM instruction barrier


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements ARM instruction barrier")
val code = """
fn instruction_sync_barrier():
    unsafe:
        asm volatile { isb }
"""
check(code.contains("isb"))
```

</details>


</details>

### RISC-V Bare-Metal Operations

<details>
<summary>Advanced: implements RISC-V semihosting</summary>

#### implements RISC-V semihosting _(slow)_

- implements RISC-V semihosting


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements RISC-V semihosting")
val code = """
fn riscv_semihost(op: u32, params: u64) -> i64:
    var result: i64
    unsafe:
        asm volatile(
            "mv a0, {op}",
            "mv a1, {params}",
            "ebreak",
            "mv {result}, a0",
            op = in(reg) op,
            params = in(reg) params,
            result = lateout(reg) result
        )
    result
"""
check(code.contains("ebreak"))
```

</details>


</details>

<details>
<summary>Advanced: implements RISC-V WFI</summary>

#### implements RISC-V WFI _(slow)_

- implements RISC-V WFI


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements RISC-V WFI")
val code = """
fn wait_for_interrupt():
    unsafe:
        asm volatile { wfi }
"""
check(code.contains("wfi"))
```

</details>


</details>

<details>
<summary>Advanced: implements RISC-V fence</summary>

#### implements RISC-V fence _(slow)_

- implements RISC-V fence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements RISC-V fence")
val code = """
fn memory_fence():
    unsafe:
        asm volatile { fence }
"""
check(code.contains("fence"))
```

</details>


</details>

### MMIO Register Access

<details>
<summary>Advanced: reads MMIO register</summary>

#### reads MMIO register _(slow)_

- reads MMIO register


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads MMIO register")
val code = """
fn mmio_read(addr: u64) -> u32:
    var value: u32
    unsafe:
        asm volatile(
            "ldr {val}, [{addr}]",
            val = out(reg) value,
            addr = in(reg) addr
        )
    value
"""
check(code.contains("ldr"))
```

</details>


</details>

<details>
<summary>Advanced: writes MMIO register</summary>

#### writes MMIO register _(slow)_

- writes MMIO register


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes MMIO register")
val code = """
fn mmio_write(addr: u64, value: u32):
    unsafe:
        asm volatile(
            "str {val}, [{addr}]",
            addr = in(reg) addr,
            val = in(reg) value
        )
"""
check(code.contains("str"))
```

</details>


</details>

<details>
<summary>Advanced: atomic MMIO update</summary>

#### atomic MMIO update _(slow)_

- atomic MMIO update


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("atomic MMIO update")
val code = """
fn mmio_set_bits(addr: u64, mask: u32):
    unsafe:
        asm volatile(
            "ldr r0, [{addr}]",
            "orr r0, r0, {mask}",
            "str r0, [{addr}]",
            addr = in(reg) addr,
            mask = in(reg) mask,
            out("r0") _
        )
"""
check(code.contains("orr"))
```

</details>


</details>

### Spinlock Implementation

<details>
<summary>Advanced: implements test-and-set spinlock</summary>

#### implements test-and-set spinlock _(slow)_

- implements test-and-set spinlock


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements test-and-set spinlock")
val code = """
fn spinlock_acquire(lock: *mut u32):
    unsafe:
        asm(
            "1:",
            "mov eax, 1",
            "xchg eax, [{lock}]",
            "test eax, eax",
            "jnz 1b",
            lock = in(reg) lock,
            out("eax") _
        )
"""
check(code.contains("xchg"))
check(code.contains("test"))
```

</details>


</details>

<details>
<summary>Advanced: implements spinlock release</summary>

#### implements spinlock release _(slow)_

- implements spinlock release


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements spinlock release")
val code = """
fn spinlock_release(lock: *mut u32):
    unsafe:
        asm volatile(
            "mov dword ptr [{lock}], 0",
            lock = in(reg) lock
        )
"""
check(code.contains("mov dword ptr"))
```

</details>


</details>

### Cache Operations

<details>
<summary>Advanced: implements cache flush (x86)</summary>

#### implements cache flush (x86) _(slow)_

- implements cache flush (x86)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements cache flush (x86)")
val code = """
fn flush_cache_line(addr: u64):
    unsafe:
        asm volatile(
            "clflush [{addr}]",
            addr = in(reg) addr
        )
"""
check(code.contains("clflush"))
```

</details>


</details>

<details>
<summary>Advanced: implements write-back and invalidate</summary>

#### implements write-back and invalidate _(slow)_

- implements write-back and invalidate


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements write-back and invalidate")
val code = """
fn cache_wbinvd():
    unsafe:
        asm volatile { wbinvd }
"""
check(code.contains("wbinvd"))
```

</details>


</details>

### Atomic Operations

<details>
<summary>Advanced: implements compare-and-swap</summary>

#### implements compare-and-swap _(slow)_

- implements compare-and-swap


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements compare-and-swap")
val code = """
fn atomic_cas(ptr: *mut u32, expected: u32, desired: u32) -> bool:
    var old: u32
    unsafe:
        asm volatile(
            "lock cmpxchg [{ptr}], {desired}",
            ptr = in(reg) ptr,
            desired = in(reg) desired,
            inout("eax") expected => old
        )
    old == expected
"""
check(code.contains("lock cmpxchg"))
```

</details>


</details>

<details>
<summary>Advanced: implements atomic increment</summary>

#### implements atomic increment _(slow)_

- implements atomic increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements atomic increment")
val code = """
fn atomic_inc(ptr: *mut u32):
    unsafe:
        asm volatile(
            "lock inc dword ptr [{ptr}]",
            ptr = in(reg) ptr
        )
"""
check(code.contains("lock inc"))
```

</details>


</details>

<details>
<summary>Advanced: implements atomic exchange</summary>

#### implements atomic exchange _(slow)_

- implements atomic exchange


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implements atomic exchange")
val code = """
fn atomic_swap(ptr: *mut u32, new_val: u32) -> u32:
    var old: u32
    unsafe:
        asm(
            "xchg [{ptr}], {val}",
            ptr = in(reg) ptr,
            val = inout(reg) new_val => old
        )
    old
"""
check(code.contains("xchg"))
```

</details>


</details>

### Context Switching

<details>
<summary>Advanced: saves registers for context switch</summary>

#### saves registers for context switch _(slow)_

- saves registers for context switch


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("saves registers for context switch")
val code = """
fn save_context(ctx: *mut Context):
    unsafe:
        asm(
            "mov [rdi + 0], rax",
            "mov [rdi + 8], rbx",
            "mov [rdi + 16], rcx",
            in("rdi") ctx,
            out("rax") _,
            out("rbx") _,
            out("rcx") _
        )
"""
check(code.contains("mov [rdi"))
```

</details>


</details>

<details>
<summary>Advanced: restores registers for context switch</summary>

#### restores registers for context switch _(slow)_

- restores registers for context switch


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("restores registers for context switch")
val code = """
fn restore_context(ctx: *Context):
    unsafe:
        asm(
            "mov rax, [rdi + 0]",
            "mov rbx, [rdi + 8]",
            "mov rcx, [rdi + 16]",
            in("rdi") ctx,
            out("rax") _,
            out("rbx") _,
            out("rcx") _
        )
"""
check(code.contains("mov rax, [rdi"))
```

</details>


</details>

### Timer Operations

<details>
<summary>Advanced: reads TSC timestamp counter</summary>

#### reads TSC timestamp counter _(slow)_

- reads TSC timestamp counter


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads TSC timestamp counter")
val code = """
fn read_tsc() -> u64:
    var low: u32
    var high: u32
    unsafe:
        asm(
            "rdtsc",
            low = out("eax") low,
            high = out("edx") high
        )
    ((high as u64) << 32) | (low as u64)
"""
check(code.contains("rdtsc"))
```

</details>


</details>

<details>
<summary>Advanced: reads RDTSCP with core ID</summary>

#### reads RDTSCP with core ID _(slow)_

- reads RDTSCP with core ID


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads RDTSCP with core ID")
val code = """
fn read_tscp() -> (u64, u32):
    var low: u32
    var high: u32
    var core: u32
    unsafe:
        asm(
            "rdtscp",
            low = out("eax") low,
            high = out("edx") high,
            core = out("ecx") core
        )
    (((high as u64) << 32) | (low as u64), core)
"""
check(code.contains("rdtscp"))
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 31 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `66a210a359a1a40c5f48e6fc00e55c5cdc66f6e81d637c75199219ed6b6e2c67`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66a210a359a1a40c5f48e6fc00e55c5cdc66f6e81d637c75199219ed6b6e2c67`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66a210a359a1a40c5f48e6fc00e55c5cdc66f6e81d637c75199219ed6b6e2c67`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/baremetal/inline_asm_integration_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/inline_asm_integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/inline_asm_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/inline_asm_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/inline_asm_integration_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements outb for serial port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/inline_asm_integration_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements inb for serial port status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/inline_asm_integration_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements outw for 16-bit I/O' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
