# Inline Asm Integration Specification

check(code.contains("out dx, al"))

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/inline_asm_integration_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 31 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

check(code.contains("out dx, al"))
        check(code.contains("COM1_PORT"))

    slow_it "implements inb for serial port status":
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

check(code.contains("out dx, eax"))
        check(code.contains("out dx, ax"))

describe "x86 CPU Control":
    slow_it "implements CLI to disable interrupts":
        val code = """
        fn disable_interrupts():
            unsafe:
                asm volatile("cli")

check(code.contains("sti"))

    slow_it "implements HLT to halt CPU":
        val code = """
        fn halt():
            unsafe:
                asm volatile("hlt")

check(code.contains("lgdt"))

    slow_it "implements LIDT to load IDT":
        val code = """
        fn load_idt(idt_ptr: u64):
            unsafe:
                asm volatile(
                    "lidt [{ptr}]",
                    ptr = in(reg) idt_ptr
                )

check(code.contains("mov"))
        check(code.contains("cr0"))

    slow_it "writes CR3 page directory":
        val code = """
        fn load_page_directory(addr: u32):
            unsafe:
                asm volatile(
                    "mov cr3, {addr}",
                    addr = in(reg) addr
                )

check(code.contains("bkpt #0xAB"))
        check(code.contains("mov r0"))

    slow_it "implements ARM WFI (wait for interrupt)":
        val code = """
        fn wait_for_interrupt():
            unsafe:
                asm volatile("wfi")

check(code.contains("dmb"))

    slow_it "implements ARM instruction barrier":
        val code = """
        fn instruction_sync_barrier():
            unsafe:
                asm volatile("isb")

check(code.contains("ebreak"))

    slow_it "implements RISC-V WFI":
        val code = """
        fn wait_for_interrupt():
            unsafe:
                asm volatile("wfi")

check(code.contains("fence"))

describe "MMIO Register Access":
    slow_it "reads MMIO register":
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

check(code.contains("str"))

    slow_it "atomic MMIO update":
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

check(code.contains("xchg"))
        check(code.contains("test"))

    slow_it "implements spinlock release":
        val code = """
        fn spinlock_release(lock: *mut u32):
            unsafe:
                asm volatile(
                    "mov dword ptr [{lock}], 0",
                    lock = in(reg) lock
                )

check(code.contains("clflush"))

    slow_it "implements write-back and invalidate":
        val code = """
        fn cache_wbinvd():
            unsafe:
                asm volatile("wbinvd")

check(code.contains("lock cmpxchg"))

    slow_it "implements atomic increment":
        val code = """
        fn atomic_inc(ptr: *mut u32):
            unsafe:
                asm volatile(
                    "lock inc dword ptr [{ptr}]",
                    ptr = in(reg) ptr
                )

check(code.contains("xchg"))

describe "Context Switching":
    slow_it "saves registers for context switch":
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

check(code.contains("mov rax, [rdi"))

describe "Timer Operations":
    slow_it "reads TSC timestamp counter":
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

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/inline_asm_integration/result.json` |

## Scenarios

- [slow] implements outb for serial port
- [slow] implements inb for serial port status
- [slow] implements outw for 16-bit I/O
- [slow] implements CLI to disable interrupts
- [slow] implements STI to enable interrupts
- [slow] implements HLT to halt CPU
- [slow] implements LGDT to load GDT
- [slow] implements LIDT to load IDT
- [slow] reads CR0 control register
- [slow] writes CR3 page directory
- [slow] implements ARM semihosting call
- [slow] implements ARM WFI (wait for interrupt)
- [slow] implements ARM data barrier
- [slow] implements ARM instruction barrier
- [slow] implements RISC-V semihosting
- [slow] implements RISC-V WFI
- [slow] implements RISC-V fence
- [slow] reads MMIO register
- [slow] writes MMIO register
- [slow] atomic MMIO update
- [slow] implements test-and-set spinlock
- [slow] implements spinlock release
- [slow] implements cache flush (x86)
- [slow] implements write-back and invalidate
- [slow] implements compare-and-swap
- [slow] implements atomic increment
- [slow] implements atomic exchange
- [slow] saves registers for context switch
- [slow] restores registers for context switch
- [slow] reads TSC timestamp counter
- [slow] reads RDTSCP with core ID
