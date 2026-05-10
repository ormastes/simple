# Local Research: SimpleOS Multi-Platform Build

Date: 2026-04-20

## Findings

- `src/os/qemu_runner.spl` already defines six QEMU targets and accepts `x86_32`, `x86`, `i386`, and `i686` aliases for `Architecture.X86`.
- `examples/simple_os/build.spl` only enumerated four targets, so x86_32 and arm32 were skipped by the example multi-architecture builder.
- `src/os/port/simpleos_native_build_config.spl` exposed SimpleOS native build helpers but only listed x86_64, aarch64, riscv64gc, and riscv32imac targets.
- `examples/simple_os/arch/x86_32/boot/` already contains the required C and assembly boot support:
  - `crt0.s`
  - `baremetal_stubs.c`
- `src/os/kernel/arch/x86_32/` already contains kernel boot, console, CPU, interrupt, paging, timer, and context modules.
- `src/os/build.sdn` already had an x86_32 target stanza, but it did not record C/ASM boot source lists or freestanding compiler flags.
- `doc/07_guide/platform/platforms.md` incorrectly stated that 32-bit systems are not supported without distinguishing hosted compiler binaries from SimpleOS guest targets.

## Implementation Direction

Create a shared SimpleOS platform-build catalog and make `simpleos_native_build_config.spl`, `examples/simple_os/build.spl`, docs, and SDN target metadata align with it. Treat `i686-simpleos` as the canonical 32-bit x86 SimpleOS target and keep `x86_32`, `x86`, `i386`, and `i686` as aliases.

## Codex RISC-V Follow-Up — 2026-04-21

<!-- codex-research -->

Spawned local research found that RISC-V OS/QEMU support already exists in `src/os/qemu_runner.spl`, `src/os/machine_profile.spl`, `src/os/kernel/arch/riscv64/`, and `src/os/kernel/arch/riscv32/`. The risky duplication is target policy drift: RISC-V ISA, ABI, QEMU CPU, and linker flags appear in the Simple platform catalog, Rust native linker, scripts, and generated docs.

The native freestanding linker already chooses `riscv32-unknown-elf` plus `-march=rv32imac -mabi=ilp32`, which is the correct no-FPU RV32 soft-float ABI. The gap was runtime correctness: unresolved compiler-rt/libgcc helper symbols such as `__adddf3`, `__fixunsdfdi`, and `__muldi3` could be weak-stubbed by the freestanding unresolved-symbol safety path. That would make soft-float programs link but compute incorrect results.

Implementation direction: make RV32 soft-float explicit in `src/os/port/simpleos_multiplatform_build.spl`, expose helper APIs through `simpleos_native_build_config.spl`, and make the Rust freestanding linker link compiler-rt builtins for RISC-V while excluding compiler-rt helper names from weak stub generation.
