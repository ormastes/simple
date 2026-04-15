# Known Limitations: SimpleOS Multi-Architecture Build Targets

**Date:** 2026-03-27
**Feature:** [os_multi_arch](../../plan/requirement/os_multi_arch.md)

---

## LIM-001: All HAL methods use pass_todo()

**Severity:** Expected (stub phase)
**Description:** Every HAL function in both x86_32 and arm32 modules uses `pass_todo()` for the method body. No actual hardware register access, memory-mapped I/O, or interrupt handling is implemented. These are structural stubs that define the correct interfaces and types but do not perform real work.

## LIM-002: x86_32 paging limited to 4GB (no PAE)

**Severity:** Low
**Description:** The x86_32 paging implementation uses 2-level page tables (Page Directory + Page Table) without Physical Address Extension. This limits the addressable physical memory to 4GB. PAE would allow up to 64GB but adds significant complexity (3-level tables, 64-bit PTEs). Acceptable for the target use case.

## LIM-003: ARM32 targets Cortex-A only, not Cortex-M

**Severity:** Low
**Description:** The arm32 HAL targets Cortex-A15 (application profile with MMU, GIC, full 32-bit ARM ISA). Cortex-M (microcontroller profile) uses a fundamentally different programming model: no MMU, NVIC instead of GIC, Thumb-only ISA, different vector table format. Supporting Cortex-M would require a separate HAL variant.

## LIM-004: mod.spl convenience aliases hardcoded to x86_64 return types

**Severity:** Medium
**Description:** The top-level `mod.spl` convenience functions (e.g., `init_console()`, `init_cpu()`) return x86_64-specific types. These aliases are not polymorphic over the target architecture. Callers needing other architectures must use the arch-specific modules directly or the dispatch functions with explicit architecture parameters.

## LIM-005: CLI integration not yet wired

**Severity:** Medium
**Description:** The `os build`, `os run`, and `os test` CLI subcommands do not yet accept `--arch x86_32` or `--arch arm32` flags. The build system and QEMU runner support these architectures internally, but there is no user-facing CLI path to invoke them. This is planned for Phase 6.

## LIM-006: No actual QEMU boot testing performed

**Severity:** Medium
**Description:** While `qemu_runner.spl` generates correct QEMU command lines for all 6 architectures (verified by inspection), no actual QEMU boot has been attempted for x86_32 or arm32 targets. The HAL stubs would need at minimum a working boot.spl and linker.ld to produce a bootable image. This is planned for Phase 7.
