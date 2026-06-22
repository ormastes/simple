# Inline Assembly Integration

> Tests inline assembly integration with the Simple compiler including register constraints, clobber lists, and memory operands. Verifies that inline asm blocks are correctly emitted and that the compiler respects assembly side effects.

<!-- sdn-diagram:id=inline_asm_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inline_asm_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inline_asm_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inline_asm_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. fn serial write byte
2. in
3. in
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn serial can write
2. out
3. in
4.
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn pci write config
2. in
3. in
4. in
5. in
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn disable interrupts
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: implements STI to enable interrupts</summary>

#### implements STI to enable interrupts _(slow)_

1. fn enable interrupts
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: implements HLT to halt CPU</summary>

#### implements HLT to halt CPU _(slow)_

1. fn halt
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn load gdt
2. ptr = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn load idt
2. ptr = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn read cr0
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn load page directory
2. addr = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn arm semihost
2. op = in
3. params = in
4. result = lateout
5. clobber abi
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn wait for interrupt
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: implements ARM data barrier</summary>

#### implements ARM data barrier _(slow)_

1. fn data memory barrier
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn instruction sync barrier
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn riscv semihost
2. op = in
3. params = in
4. result = lateout
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn wait for interrupt
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
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


</details>

<details>
<summary>Advanced: implements RISC-V fence</summary>

#### implements RISC-V fence _(slow)_

1. fn memory fence
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn mmio read
2. addr = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn mmio write
2. addr = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn mmio set bits
2. addr = in
3. mask = in
4. out
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn spinlock acquire
2. lock = in
3. out
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn spinlock release
2. lock = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn flush cache line
2. addr = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn cache wbinvd
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn atomic cas
2. ptr = in
3. desired = in
4. inout
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn atomic inc
2. ptr = in
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn atomic swap
2. ptr = in
3. check


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

1. fn save context
2. in
3. out
4. out
5. out
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn restore context
2. in
3. out
4. out
5. out
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn read tsc
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

1. fn read tscp
2. low = out
3. high = out
4. core = out
5.
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
