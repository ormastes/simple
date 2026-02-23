# Baremetal Platform Specifications

Mirrors: `test/feature/baremetal/`
Generated: `doc/spec/feature/baremetal/`

13 spec files covering bare-metal platform support: ARM, ARM64, RISC-V, x86/x86_64
architectures, boot sequences, semihosting, and hardware abstraction.

## Spec Files

| Spec File | Coverage |
|-----------|----------|
| `allocator_spec.spl` | Memory allocator tests |
| `arm32_boot_spec.spl` | ARM32 boot sequence |
| `arm64_boot_spec.spl` | ARM64/AArch64 boot sequence |
| `boot_test_spec.spl` | Generic boot test |
| `debug_boot_spec.spl` | Debug boot mode |
| `hello_riscv32_semihost_spec.spl` | RISC-V 32 semihosting via QEMU |
| `inline_asm_integration_spec.spl` | Inline assembly integration |
| `interrupt_spec.spl` | Interrupt handling |
| `riscv64_boot_spec.spl` | RISC-V 64 boot sequence |
| `startup_spec.spl` | Startup/init sequence |
| `syscall_spec.spl` | Syscall interface |
| `x86_64_boot_spec.spl` | x86_64 boot sequence |
| `x86_boot_spec.spl` | x86 (32-bit) boot sequence |

## QEMU Test Binaries

Pre-built ELF binaries in `examples/09_embedded/baremetal/baremetal/`:

| Binary | Arch | Purpose |
|--------|------|---------|
| `hello_riscv32_semihost.elf` | RV32I | Basic semihosting hello world |
| `hello_riscv32_sspec.elf` | RV32I | SSpec-format output for test runner |

Build with: `examples/09_embedded/baremetal/baremetal/build.ssh`

Run: `qemu-system-riscv32 -M virt -bios none -kernel <elf> -nographic -semihosting-config enable=on,target=native`
