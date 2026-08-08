# Requirements: SimpleOS Multi-Platform Build

Date: 2026-04-20

## Scope

REQ-SMPB-001: SimpleOS must expose a canonical platform-build catalog for supported guest targets.

REQ-SMPB-002: The catalog must include `i686-simpleos` as the canonical 32-bit x86 SimpleOS target.

REQ-SMPB-003: The 32-bit x86 target must resolve aliases `x86_32`, `x86`, `i386`, and `i686`.

REQ-SMPB-004: The 32-bit x86 target must record freestanding C flags, freestanding ASM flags, C boot sources, ASM boot sources, linker script, output path, and QEMU defaults.

REQ-SMPB-005: Native SimpleOS build helpers must derive supported targets, architecture names, clang targets, C flags, ASM flags, and boot source lists from the platform-build catalog.

REQ-SMPB-006: The example SimpleOS multi-architecture builder must enumerate all first-class QEMU targets instead of a stale hardcoded subset.

REQ-SMPB-007: Documentation must distinguish hosted Simple compiler platform support from SimpleOS guest target support.

REQ-SMPB-008: The platform-build catalog must record RISC-V ISA, ABI, and floating-point ABI policy so RV32 no-FPU support is visible to callers instead of encoded only in compiler flags.

REQ-SMPB-009: The `riscv32imac-simpleos` target must use RV32IMAC, ILP32, and soft-float metadata and C flags.

REQ-SMPB-010: Freestanding native links must resolve compiler-generated soft-float and integer helper symbols from compiler-rt/libgcc rather than weak-stubbing those helpers.

REQ-SMPB-011: RISC-V SimpleOS QEMU build paths must default to an LLVM-enabled native-build backend unless the caller explicitly overrides the backend for diagnostics.

REQ-SMPB-012: RISC-V SimpleOS boot/runtime support must be implemented in Simple source with embedded assembly, not arch-local C or standalone assembly boot files.

REQ-SMPB-013: RISC-V 32-bit and 64-bit console setup must share common 16550 MMIO logic where the QEMU virt hardware contract is identical.
