# SimpleOS Multi-Platform Build Architecture

Status: active  
Date: 2026-04-20

## Problem

SimpleOS has architecture-specific kernel sources and QEMU runners for x86_64, x86_32, ARM64, ARM32, RISC-V 64, and RISC-V 32, but build metadata was split across `qemu_runner.spl`, `simpleos_native_build_config.spl`, `src/os/build.sdn`, and example scripts. That made 32-bit x86 easy to miss even though the boot and HAL directories already existed.

## Decision

Use `src/os/port/simpleos_multiplatform_build.spl` as the canonical SimpleOS platform-build catalog.

The catalog owns:

- canonical target name and aliases
- `Architecture` enum value and bit width
- Simple native target triple and clang C/ASM target triple
- entrypoint, linker script, output path, source roots
- C boot sources and assembly boot sources
- freestanding C flags, freestanding ASM flags, and target link hints
- QEMU binary, machine, and CPU defaults

`simpleos_native_build_config.spl` delegates target names, architecture extraction, clang target selection, C flags, ASM flags, and boot-source discovery to the catalog. `examples/simple_os/build.spl` enumerates `get_all_targets()` so the example builder cannot silently drift back to four targets.

`src/os/qemu_runner.spl` selects LLVM automatically for `Architecture.X86` when `SIMPLE_OS_BUILD_BACKEND` is unset, because the Cranelift backend in this toolchain does not provide an i686 freestanding object target. An explicit `SIMPLE_OS_BUILD_BACKEND=cranelift` still wins for diagnostics.

The LLVM path requires the selected Simple compiler binary to be built with the Rust `llvm` feature. On this toolchain that also requires LLVM 18 discovery through `LLVM_SYS_180_PREFIX` or an equivalent system install.

## 32-bit x86

The 32-bit x86 lane is canonicalized as `i686-simpleos` with aliases `x86_32`, `x86`, `i386`, and `i686`.

Build rules:

- C target: `--target=i686-unknown-none-elf`
- C mode: `-m32 -march=i686 -ffreestanding -nostdlib`
- ASM target: `--target=i686-unknown-none-elf`
- ASM mode: `-m32 -march=i686 -ffreestanding`
- boot C source: `examples/simple_os/arch/x86_32/boot/baremetal_stubs.c`
- boot ASM source: `examples/simple_os/arch/x86_32/boot/crt0.s`
- linker mode hint: `elf_i386`
- QEMU: `qemu-system-i386`
- default SimpleOS build backend: LLVM

## Boundary

Hosted Simple compiler binaries remain 64-bit host artifacts. SimpleOS guest targets may be 32-bit or 64-bit. Documentation must avoid saying “32-bit is unsupported” without qualifying whether it refers to hosted compiler binaries or SimpleOS guest binaries.

## Follow-Up

The catalog is now ready for a future object pipeline that compiles `boot_c_sources` and `boot_asm_sources` into per-target objects before final native link. The current change exposes the metadata and validates it through unit tests; it does not replace the lower-level linker or native backend.

## RISC-V Soft-Float Update

<!-- codex-design -->

RISC-V target policy is owned in two layers:

- `src/os/port/simpleos_multiplatform_build.spl` owns user-visible SimpleOS platform metadata: ISA, ABI, floating-point ABI, QEMU profile, and freestanding compiler flags.
- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` owns final freestanding ELF linking for the bootstrap native-build path.

`riscv32imac-simpleos` is explicitly RV32IMAC + ILP32 + soft-float. The platform catalog exposes this through helper APIs so tests and callers do not need to parse `-march` or `-mabi` strings.

The freestanding linker must not satisfy compiler-rt/libgcc helper symbols through weak unresolved-symbol stubs. Those helpers are runtime semantics, especially for RV32 float emulation. The linker asks clang for the target builtins archive with `--target=<triple> -print-libgcc-file-name`, adds it to the freestanding link, and filters compiler-rt helper names out of stub generation.

RISC-V SimpleOS QEMU builds default to LLVM native-build because the current Cranelift path cannot initialize the freestanding RISC-V object target. `SIMPLE_OS_BUILD_BACKEND=cranelift` remains available as an explicit diagnostic override.

## RISC-V Simple Runtime Conversion

<!-- codex-design -->

RISC-V boot/runtime code is now owned by Simple modules under `src/os/kernel/arch/riscv32` and `src/os/kernel/arch/riscv64`. The platform catalog keeps `boot_c_sources` and `boot_asm_sources` empty for both RISC-V targets, so native-build cannot silently reintroduce `examples/simple_os/arch/riscv*/boot` C or assembly objects.

RV64 hardware entry and trap entry are `@naked` Simple functions with embedded assembly. `_start` lives with the RV64 boot module; `_rv64_trap_vector` and `_rv64_enter_user` live in `trap_vector.spl` and preserve the existing trap-frame ABI used by `interrupt.spl`.

The duplicated RISC-V 16550 UART setup is factored into `src/os/kernel/boot/uart16550_mmio.spl`. RV32 and RV64 pass their QEMU virt MMIO base address to the shared helper; x86_64 remains separate because it uses port I/O rather than MMIO for its early serial path.

## Shared Pure-Simple Console Adapters

<!-- codex-design -->

The architecture tree now prefers family-level Simple helpers for MMIO peripherals that are identical across 32-bit and 64-bit variants:

- RISC-V: `src/os/kernel/arch/riscv/console_common.spl` centralizes QEMU virt 16550 init, read, and write behavior.
- ARM: `src/os/kernel/arch/arm/pl011_common.spl` centralizes QEMU virt PL011 register programming and blocking writes.
- x86: `src/os/kernel/arch/x86/com1_common.spl` centralizes COM1 port setup and blocking writes for x86_32 and x86_64.

Leaf modules under `riscv32`, `riscv64`, `arm32`, `arm64`, `x86_32`, and `x86_64` are HAL adapters. They preserve public symbol names and target-specific compatibility behavior while delegating duplicate register logic to the shared Simple helpers.
