# MLK-S02-100T Product Guide

## Board Identity

- **Board:** MLK-S02-100T
- **FPGA:** XC7A100T-2FFG484I (Xilinx Artix-7 100T)
- **Package:** FFG484, speed grade -2

## Status

**SCAFFOLD ONLY.** No real hardware run has been completed on this board.

To proceed, you must obtain the vendor-authoritative XDC pin constraints,
board schematic, and reference designs. See:
`doc/07_guide/hardware/mlk_s02_100t_vendor_download_guide.md`

## Available Scaffolds

The following files exist as starting points but contain placeholder or
commented-out content until vendor files are obtained:

| File | Purpose |
|------|---------|
| `examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc` | Commented XDC template |
| `examples/09_embedded/fpga_riscv/rtl/mlk_s02_100t_wrapper_stub.vhd` | Wrapper stub |
| `examples/09_embedded/fpga_riscv/build_mlk_s02_100t.tcl` | Vivado project scaffold |
| `examples/09_embedded/fpga_riscv/program_mlk_s02_100t.tcl` | Programming scaffold |

## Before First Use

You **must** obtain authoritative vendor files before attempting any build:

1. Download the official XDC pin-constraint file from the board vendor.
2. Obtain the board schematic PDF for pin verification.
3. Acquire any vendor reference designs for clock, memory, and I/O.

Follow the step-by-step instructions in:
`doc/07_guide/hardware/mlk_s02_100t_vendor_download_guide.md`

## Build Flow

Once vendor files have been obtained and the XDC is populated:

```bash
cd examples/09_embedded/fpga_riscv
vivado -mode batch -source build_mlk_s02_100t.tcl
vivado -mode batch -source program_mlk_s02_100t.tcl
```

## Generated Linux Boot Variants

The build system can generate two Linux boot configurations for this board:

- **`mlk_s02_100t_rv32_linux`** -- RV32 Linux on Artix-7
- **`mlk_s02_100t_rv64_linux`** -- RV64 Linux on Artix-7

## Related Files

- Board facts: `config/resources/boards/mlk_s02_100t.sdn`
- Bringup guide: `doc/07_guide/hardware/xilinx_fpga_board_bringup.md`
- Vendor download guide: `doc/07_guide/hardware/mlk_s02_100t_vendor_download_guide.md`
