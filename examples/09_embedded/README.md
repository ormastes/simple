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
Hardware description language examples:
- **alu.spl** - Arithmetic Logic Unit
- **counter.spl** - Counter circuit
- **fsm.spl** - Finite State Machine
