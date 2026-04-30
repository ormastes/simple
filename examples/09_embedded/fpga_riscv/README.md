# FPGA RISC-V CPU Project

Handwritten RV32I single-cycle CPU with semihosting, validated in GHDL simulation and carrying a historical ZedBoard-specific Vivado wrapper.

This directory is the current in-repo runnable RTL CPU lane. It is not generated from
Simple today. Repo-native generated RV32/RV64 work lives under `src/hardware/` as
contract/orchestration code, while Linux-capable RTL proof currently comes from
explicit external reference lanes (`reference_external_rv32_linux`,
`reference_external_rv64_linux`).

## Support Status

- GHDL simulation is the verified path for this handwritten RV32I lane.
- `build.tcl`, `program.tcl`, and `constraints/zedboard.xdc` are ZedBoard-specific historical bring-up assets.
- The repo now records known board facts for `MLK-S02-100T` in `config/resources/boards/mlk_s02_100t.sdn` and ships a commented constraint scaffold in `constraints/mlk_s02_100t.xdc`, but it does not yet ship a verified `MLK-S02-100T` pin map or programming flow.
- The repo also ships board-wrapper and Vivado script scaffolds for `MLK-S02-100T`, but they remain non-verified templates until the real XDC and top-level wiring land.
- The repo-native generated FPGA manifest still defaults to `xilinx_generic` with `BOARD_PART_TBD`, so a concrete board must be selected before claiming hardware boot support.

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

## Historical ZedBoard Deployment (requires Vivado)

This flow is board-specific and should not be treated as proof that FPGA hardware support is currently validated in the repo's public lane set.

```bash
cd examples/09_embedded/fpga_riscv
vivado -mode batch -source build.tcl     # synthesize
vivado -mode batch -source program.tcl   # flash
```

For `MLK-S02-100T` or other new Artix-7 100T boards, use the bring-up guide in `doc/07_guide/hardware/xilinx_fpga_board_bringup.md` instead of reusing the ZedBoard files unchanged.

Current `MLK-S02-100T` scaffolds:
- `constraints/mlk_s02_100t.xdc`
- `rtl/mlk_s02_100t_wrapper_stub.vhd`
- `build_mlk_s02_100t.tcl`
- `program_mlk_s02_100t.tcl`

## Platform Cable USB II

Firmware auto-loads via udev rule (`/etc/udev/rules.d/99-xilinx-platform-cable.rules`).
Manual: `fxload -t fx2lp -I /etc/xilinx-xusb/xusbdfwu.hex -D /dev/bus/usb/001/XXX`
