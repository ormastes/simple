# Design: SimpleOS Multi-Architecture Build Targets

**Date:** 2026-03-27
**Requirement:** [os_multi_arch](../plan/requirement/os_multi_arch.md)

---

## Module Structure

Each architecture provides 9 HAL files following an identical interface contract:

```
src/os/kernel/arch/
  x86_32/
    mod.spl          # Re-exports, arch-specific constants
    boot.spl         # Multiboot 1 entry, stack setup
    console.spl      # VGA text mode (0xB8000)
    cpu.spl          # GDT, ring transitions, halt
    paging.spl       # 2-level (PD/PT), 4KB pages, 4GB limit
    interrupt.spl    # IDT, PIC 8259 (master+slave)
    timer.spl        # PIT 8254 channel 0, IRQ0
    context.spl      # X86Context (u32 registers)
    linker.ld        # 1MB load address, Multiboot header
  arm32/
    mod.spl          # Re-exports, arch-specific constants
    boot.spl         # ARM vector table, stack init
    console.spl      # PL011 UART (0x09000000)
    cpu.spl          # CP15 coprocessor, WFI halt
    paging.spl       # Short-descriptor (16KB L1, 1KB L2), 4KB pages
    interrupt.spl    # GICv2 distributor + CPU interface
    timer.spl        # ARM Generic Timer (CNTP)
    context.spl      # Arm32Context (u32 registers)
    linker.ld        # 0x40000000 load address (virt machine)
```

---

## Type Definitions

### X86Context

32-bit register file for context switching:

| Field | Type | Description |
|-------|------|-------------|
| eax, ebx, ecx, edx | u32 | General-purpose registers |
| esi, edi | u32 | Index registers |
| esp, ebp | u32 | Stack/frame pointer |
| eip | u32 | Instruction pointer |
| eflags | u32 | CPU flags |
| cs, ds, es, fs, gs, ss | u32 | Segment selectors |

### Arm32Context

ARM register file for context switching:

| Field | Type | Description |
|-------|------|-------------|
| r0-r12 | u32 | General-purpose registers |
| sp (r13) | u32 | Stack pointer |
| lr (r14) | u32 | Link register |
| pc (r15) | u32 | Program counter |
| cpsr | u32 | Current program status register |
| spsr | u32 | Saved program status register |

---

## Key Technical Decisions

### x86_32

1. **Multiboot 1** (not Multiboot 2) — simpler header, sufficient for QEMU `-kernel` loading
2. **2-level paging** (PD + PT) — no PAE; limits address space to 4GB, which is acceptable for an educational/embedded OS
3. **PIC 8259** (not APIC) — legacy interrupt controller; simpler to implement, works on all x86 targets including QEMU's default i386 machine
4. **PIT 8254** — channel 0 for system timer via IRQ0; standard 1.193182 MHz base frequency

### ARM32

1. **Cortex-A15** target (not Cortex-M3) — runs on QEMU `virt` machine with full MMU support; Cortex-M is a fundamentally different programming model (no MMU, different vector table)
2. **GICv2** — Generic Interrupt Controller v2; standard for Cortex-A cores on QEMU virt
3. **Short-descriptor paging** — 16KB L1 table (4096 entries), 1KB L2 tables (256 entries), 4KB page granularity
4. **PL011 UART** — standard serial console at 0x09000000 on QEMU virt machine

---

## Integration Points

| Component | File | Change |
|-----------|------|--------|
| Architecture enum | arch_context.spl | Added `X86` and `Arm32` variants |
| Build targets | build.sdn | Added `x86_32` and `arm32` target sections with QEMU binary, machine type, CPU model |
| MDSOC capsules | capsule.sdn | Added `arch_x86_32` and `arch_arm32` capsules in transform dimension |
| Arch dispatch | mod.spl | Added imports for x86_32 and arm32 modules; extended match arms in dispatch functions |
| QEMU runner | qemu_runner.spl | Extended get_qemu_binary, get_machine_flags, get_cpu_flags, run_qemu for 6 arches |

---

## Cross-References

- **Requirement:** [doc/02_requirements/feature/os_multi_arch.md](../plan/requirement/os_multi_arch.md)
- **Limitations:** [doc/08_tracking/bug/os_multi_arch_limitations.md](../tracking/bug/os_multi_arch_limitations.md)
