# Non-FPGA Development Board Reference

Non-FPGA development boards and emulators used in the Simple Language project.

## Overview

| Category | Board / Emulator | Lane | Status |
|----------|-----------------|------|--------|
| Emulator | QEMU RV32 | `qemu_rv32_semihost` | stable |
| Emulator | QEMU RV64 | `qemu_rv64_semihost` | in_progress |
| Emulator | QEMU ARM | `qemu_arm_semihost` | stable |
| Emulator | x86_64 Direct Boot | `x86_64_direct_boot` | stable |
| Emulator | GHDL RV32 | `ghdl_rv32_semihost`, `ghdl_rv32_mailbox` | host_aware |
| ARM | STM32H7x3I-EVAL | `stm32h7_openocd` | host_aware |
| ARM | STM32WB Nucleo | `stm32wb_openocd` | host_aware |
| ARM | Arduino UNO R4 WiFi | `arduino_r4_cmsis_dap` | in_progress |
| RISC-V | CH32V307 | `ch32v307_wlink` | host_aware |
| Other | ESP32 | `esp32_usb_jtag` | in_progress |

## Emulators (No Hardware Required)

### QEMU RV32

- **Lane:** `qemu_rv32_semihost`
- **Status:** stable
- Uses `qemu-system-riscv32` with semihosting
- Primary target for baremetal and SimpleOS testing

### QEMU RV64

- **Lane:** `qemu_rv64_semihost`
- **Status:** in_progress
- Uses `qemu-system-riscv64` with semihosting

### QEMU ARM

- **Lane:** `qemu_arm_semihost`
- **Status:** stable
- Uses `qemu-system-arm` with semihosting

### x86_64 Direct Boot

- **Lane:** `x86_64_direct_boot`
- **Status:** stable
- Native execution, Limine bootloader for SimpleOS

### GHDL RV32

- **Lanes:** `ghdl_rv32_semihost`, `ghdl_rv32_mailbox`
- **Status:** host_aware
- VHDL simulation of handwritten RV32I core

## ARM Boards

### STM32H7x3I-EVAL

- **Lane:** `stm32h7_openocd`
- **Status:** host_aware
- Cortex-M7, OpenOCD JTAG
- Also available via TRACE32 lane

### STM32WB Nucleo

- **Lane:** `stm32wb_openocd`
- **Status:** host_aware
- Dual-core Cortex-M4/M0+, BLE capable
- OpenOCD debugger

### Arduino UNO R4 WiFi

- **Lane:** `arduino_r4_cmsis_dap`
- **Status:** in_progress
- Renesas RA4M1 (Cortex-M4), CMSIS-DAP debugger

## RISC-V Boards

### CH32V307

- **Lane:** `ch32v307_wlink`
- **Status:** host_aware
- WCH CH32V307, RISC-V RV32IMAC
- WCH-Link debugger

## Other

### ESP32

- **Lane:** `esp32_usb_jtag`
- **Status:** in_progress
- Xtensa architecture, USB JTAG, OpenOCD

## Status Definitions

| Status | Meaning |
|--------|---------|
| stable | CI-tested, reliable |
| host_aware | Works with local hardware, not CI-tested |
| in_progress | Partially implemented |
| transport_only | Data transport works, full exec not yet |
| excluded_public | Historical, not in public builds |

## Quick Start

QEMU is the most accessible path -- no hardware required.

```bash
# RV32 semihosting (stable)
bin/simple run --target=qemu_rv32 examples/09_embedded/baremetal/hello.spl

# x86_64 SimpleOS
bin/simple run --target=x86_64 src/os/kernel/main.spl
```

## SimpleOS Targets

- **x86_64** -- Limine boot, QEMU
- **RISC-V 32/64** -- QEMU, FPGA planned

## File References

- Adapters: `src/lib/nogc_sync_mut/debug/remote/exec/adapter_*.spl`
- Lane Registry: `src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl`
- Baremetal Runtime: `src/lib/nogc_async_mut_noalloc/baremetal/`
- Embedded Examples: `examples/09_embedded/`
- Embedded Board Guide: `doc/07_guide/embedded_board_guide.md`
