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

## RISC-V Soft-Float Detail

<!-- codex-design -->

`SimpleOsPlatformBuildTarget` includes `isa`, `abi`, and `float_abi` fields. For `riscv32imac-simpleos`, these are `rv32imac`, `ilp32`, and `soft`; for `riscv64gc-simpleos`, these are `rv64gc`, `lp64d`, and `double`.

New catalog/native-build APIs:

- `simpleos_platform_isa(name)`
- `simpleos_platform_abi(name)`
- `simpleos_platform_float_abi(name)`
- `simpleos_platform_needs_soft_float_runtime(name)`
- `simpleos_target_isa(target)`
- `simpleos_target_float_abi(target)`
- `simpleos_target_needs_soft_float_runtime(target)`

The Rust freestanding link path now adds a compiler-rt/libgcc builtins archive discovered through clang and prevents helper symbols like `__adddf3` and `__fixunsdfdi` from being emitted as weak stubs.

`src/os/qemu_runner.spl` and `scripts/qemu_riscv32.shs` route RISC-V OS builds to `--backend llvm` by default so the QEMU boot lane does not fail in Cranelift target initialization before reaching the linker. The RV32 script honors `SIMPLE_BINARY` and writes build output to `build/os/build_riscv32.log`.

## RISC-V Simple Runtime Detail

<!-- codex-design -->

RISC-V platform rows intentionally keep `boot_c_sources` and `boot_asm_sources` empty. Unit coverage asserts this for `riscv64gc-simpleos` and `riscv32imac-simpleos`.

RV64 startup and trap mechanics are implemented as Simple `@naked` functions using `asm volatile:` blocks. `_start` preserves OpenSBI `a0/a1`, installs `_stack_top`, clears BSS, and calls the mangled `boot_main` symbol. `_rv64_trap_vector` saves/restores the existing `Riscv64Context` layout and calls `rv64_dispatch_trap_frame_ptr`; `_rv64_enter_user` restores a scheduler-provided context and enters U-mode with `sret`.

The shared `uart16550_mmio` helper owns 16550 register offsets, initialization, blocking TX, and optional RX. RV32 and RV64 console modules keep only readiness state, SBI fallback where applicable, and architecture-specific public names.
