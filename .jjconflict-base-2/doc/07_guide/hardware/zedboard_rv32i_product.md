# ZedBoard RV32I Product Guide

## Board Identity

- **Board:** Avnet ZedBoard
- **SoC:** Xilinx Zynq-7020 (XC7Z020-CLG484-1)
- **Architecture:** Dual ARM Cortex-A9 + Artix-7 equivalent FPGA fabric

## Status

**HISTORICAL / EXCLUDED.** The ZedBoard was used for a custom handwritten
RV32I CPU project. It is not part of the public lane set and is excluded
from public builds.

## CPU Design

Handwritten VHDL RV32I single-cycle CPU, validated with GHDL (VHDL-2008):

| File | Purpose |
|------|---------|
| `examples/09_embedded/fpga_riscv/rtl/rv32i_core.vhd` | Main RV32I core |
| `examples/09_embedded/fpga_riscv/rtl/rv32i_pkg.vhd` | Package definitions |

## Build Flow

Requires Vivado and a Platform Cable USB II for programming:

```bash
cd examples/09_embedded/fpga_riscv
vivado -mode batch -source build.tcl
vivado -mode batch -source program.tcl
```

## Debug

Debug access is provided via Platform Cable USB II through OpenOCD JTAG.

## GHDL Simulation

You can simulate the RV32I core without any hardware using GHDL:

```bash
cd examples/09_embedded/fpga_riscv
sh test/run_ghdl_tests.sh
```

## Note

Do **NOT** reuse ZedBoard scripts for other boards. Each board requires its
own XDC constraints, wrapper VHDL, and build/program Tcl scripts.

## Related Files

- Constraints: `examples/09_embedded/fpga_riscv/constraints/zedboard.xdc`
- Build script: `examples/09_embedded/fpga_riscv/build.tcl`
- Program script: `examples/09_embedded/fpga_riscv/program.tcl`
