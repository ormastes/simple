# SimpleOS Multi-Architecture Build Targets (x86_32 + ARM32)

**Date:** 2026-03-27
**Priority:** P2
**Status:** Implemented (HAL stubs complete, CLI wiring pending)

## Motivation

SimpleOS supported 4 architectures (x86_64, arm64, riscv64, riscv32). The Simple compiler already supported 6 target triples (adding x86/i686 and arm/armv7). The goal was to achieve full 6-architecture coverage in the OS kernel HAL layer, build system, and MDSOC capsule definitions so that every compiler-supported target has a corresponding OS HAL.

---

## Scope

### In Scope

- **x86_32 HAL** — 9 files in `src/os/kernel/arch/x86_32/`: mod.spl, boot.spl, console.spl, cpu.spl, paging.spl, interrupt.spl, timer.spl, context.spl, linker.ld
- **ARM32 HAL** — 9 files in `src/os/kernel/arch/arm32/`: mod.spl, boot.spl, console.spl, cpu.spl, paging.spl, interrupt.spl, timer.spl, context.spl, linker.ld
- **build.sdn** — 6 target sections (one per architecture)
- **capsule.sdn** — 6 arch capsules in the transform dimension
- **qemu_runner.spl** — 6-architecture support in all runner functions
- **mod.spl** — arch dispatch imports and match arms for all 6 architectures
- **arch_context.spl** — Architecture enum extended with X86 and Arm32 variants; type definitions for X86Context and Arm32Context

### Out of Scope

- CLI wiring (`os build`, `os run`, `os test` subcommands) — Phase 6
- Actual QEMU boot testing — Phase 7
- PAE paging for x86_32 (limited to 4GB flat address space)
- APIC support for x86_32 (uses legacy PIC 8259 only)
- Cortex-M support for ARM32 (targets Cortex-A only)

---

## Acceptance Criteria

| ID | Criterion | Status |
|----|-----------|--------|
| AC-01 | Architecture enum has 6 variants: X86_64, X86, Riscv64, Riscv32, Arm64, Arm32 | Done |
| AC-02 | Each architecture has 9 HAL files (mod, boot, console, cpu, paging, interrupt, timer, context, linker.ld) | Done |
| AC-03 | build.sdn contains 6 target sections | Done |
| AC-04 | capsule.sdn contains 6 arch capsules in the transform dimension | Done |
| AC-05 | qemu_runner.spl supports 6 architectures in all functions (get_qemu_binary, get_machine_flags, get_cpu_flags, run_qemu) | Done |
| AC-06 | mod.spl imports and dispatches for all 6 architectures | Done |

---

## Dependencies

- **arch_context.spl** — Architecture enum definition and per-arch context types
- **boot/ports.spl** — BootOutputPort trait used by all boot.spl implementations
- **hal.spl** — HAL traits (Console, Cpu, Paging, InterruptController, Timer) implemented by each arch
