# Design: SimpleOS Multi-Platform Build

Date: 2026-04-20

## Data Model

`SimpleOsPlatformBuildTarget` is the platform catalog row. It stores canonical name, aliases, architecture enum, bit width, native and clang target triples, QEMU defaults, linker script, entrypoint, output path, source roots, boot C/ASM source lists, C/ASM flags, link hints, and notes.

## APIs

- `simpleos_platform_targets()`
- `simpleos_platform_target_by_name(name)`
- `simpleos_platform_target_names()`
- `simpleos_platform_c_flags(name)`
- `simpleos_platform_asm_flags(name)`
- `simpleos_platform_boot_c_sources(name)`
- `simpleos_platform_boot_asm_sources(name)`
- `simpleos_platform_clang_target(name)`
- `simpleos_platform_arch_name(name)`

`simpleos_native_build_config.spl` delegates to these APIs and keeps the sysroot/linker helper surface stable.

## x86_32 Contract

`i686-simpleos` is the canonical target. Its aliases are `x86_32`, `x86`, `i386`, and `i686`. Its C and assembly flags both use `i686-unknown-none-elf` and `-m32`; its boot support sources are `baremetal_stubs.c` and `crt0.s`.

## Test Coverage

`test/unit/os/port/simpleos_multiplatform_build_spec.spl` verifies supported target exposure, alias resolution, i686 C/ASM flags, x86_32 boot source paths, and native build helper delegation.
