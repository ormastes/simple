# FPGA RISC-V CPU Project

RV32I single-cycle CPU with semihosting, targeting ZedBoard (Zynq-7020) and GHDL simulation.

## Quick Start

```bash
# Run semihosting test on GHDL-simulated CPU
bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_runner.shs <binary.elf>

# Run the hello world semihost test
riscv64-linux-gnu-as -march=rv32i -mabi=ilp32 -o /tmp/test.o \
    examples/09_embedded/baremetal/baremetal/hello_riscv32_semihost.s
riscv64-linux-gnu-ld -m elf32lriscv -Ttext=0x80000000 --no-relax -o /tmp/test.elf /tmp/test.o
bash src/lib/nogc_async_mut_noalloc/baremetal/ghdl_runner.shs /tmp/test.elf
```

## Architecture

Single-cycle RV32I CPU:

| Module | File | Description |
|--------|------|-------------|
| rv32i_pkg | `rtl/rv32i_pkg.vhd` | Opcodes, ALU ops, semihosting constants |
| regfile | `rtl/regfile.vhd` | 32x32 register file, SP init, a0/a1 readout |
| alu | `rtl/alu.vhd` | ADD/SUB/SLL/SLT/XOR/SRL/SRA/OR/AND |
| decoder | `rtl/decoder.vhd` | I/R/S/B/U/J decode, immediate gen, control |
| rv32i_core | `rtl/rv32i_core.vhd` | Datapath + semihosting detection |
| tb_semi_run | `rtl/tb_semi_run.vhd` | Testbench: loads program, handles semihosting I/O |

## Semihosting Support

The CPU detects the RISC-V semihosting magic sequence:
```
slli zero, zero, 0x1f   (0x01f01013)
ebreak                   (0x00100073)
srai zero, zero, 0x7    (0x40705013)
```

Supported operations:
- **SYS_WRITE0** (0x04): print null-terminated string from memory
- **SYS_WRITEC** (0x03): print single character
- **SYS_EXIT** (0x18): halt with exit code

Register convention: `a0` = operation, `a1` = parameter pointer.

## GHDL Runner

`src/lib/nogc_async_mut_noalloc/baremetal/ghdl_runner.shs` — drop-in replacement for `qemu_runner.spl`.

```bash
# Usage
./ghdl_runner.shs <binary.elf> [--timeout=30]

# Exit codes: 0=pass, 1=fail, 124=timeout
```

Pipeline: ELF → objcopy → VHDL memory init → GHDL compile → simulate → parse semihosting output.

Requires: `ghdl`, `riscv64-linux-gnu-objcopy`, `python3`.

## Memory Map

| Address | Size | Description |
|---------|------|-------------|
| 0x80000000 | 64KB | Unified RAM (code + data + stack) |
| SP init | 0x80000FFC | Stack pointer (top of 4KB in regfile) |

Programs must be linked with `-Ttext=0x80000000`.

## ZedBoard Deployment (requires Vivado)

```bash
cd examples/09_embedded/fpga_riscv
vivado -mode batch -source build.tcl     # synthesize
vivado -mode batch -source program.tcl   # flash
```

## Platform Cable USB II

Firmware auto-loads via udev rule (`/etc/udev/rules.d/99-xilinx-platform-cable.rules`).
Manual: `fxload -t fx2lp -I /etc/xilinx-xusb/xusbdfwu.hex -D /dev/bus/usb/001/XXX`
