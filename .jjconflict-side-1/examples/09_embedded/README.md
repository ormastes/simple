# Embedded Systems Examples

Baremetal programming, QEMU emulation, and hardware description.

## Baremetal (`baremetal/`)

Direct hardware programming with no OS.

### Supported Architectures
- x86_64
- ARM (32-bit)
- ARM64 (AArch64)
- RISC-V 32-bit
- RISC-V 64-bit

### Examples
- **blinky_stm32f4.spl** - LED blinker for STM32F4
- **timer_riscv32.spl** - Timer example for RISC-V

## QEMU (`qemu/`)
- **unified_runner.spl** - Unified QEMU runner for all architectures

## VHDL (`vhdl/`)
Hardware description language examples, organized by category.
See `vhdl/README.md` for details.

- **builder/** - VhdlBuilder API demos (programmatic VHDL generation)
- **backend/** - Backend-generated examples (`--backend=vhdl`, pending Phase 3-4)
- **simulation/** - Simulation fixtures and testbenches
