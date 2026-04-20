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
