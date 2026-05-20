# KV260 RV64GC FPGA Boot Guide

End-to-end guide for generating, validating, synthesizing, and booting an RV64GC SoC on the Kria KV260 (K26 SOM, xck26-sfvc784-2LV-c).

## 1. Prerequisites

| Tool | Version | Purpose |
|------|---------|---------|
| GHDL | 4.1.0+ (mcode) | VHDL-2008 analysis, elaboration, simulation |
| Vivado | 2025.2 | Synthesis, implementation, bitstream generation |
| KV260 board | K26 SOM | Target FPGA (xck26-sfvc784-2LV-c) |
| USB cables | 2x | JTAG programming + UART console (FTDI FT4232H) |
| Simple compiler | v1.0.0-beta+ | `bin/simple` for VHDL generation |

```bash
# Verify tools
ghdl --version
source ~/Xilinx/2025.2/Vivado/settings64.sh
vivado -version
bin/simple --version
```

## 2. VHDL Generation

Generate all RV64GC SoC VHDL files from Simple RTL models:

```bash
sh scripts/fpga/generate_rv64_vhdl.shs
```

Output directory: `build/vhdl/rv64/`

Generated files:
- `soc_top_rv64.vhd` — Top-level SoC entity (Wishbone bus, peripherals)
- `pkg.vhd` — RV64GC package definitions
- `alu.vhd`, `regfile.vhd`, `csr_s.vhd`, `csr.vhd` — Leaf modules
- `decode.vhd`, `lsu.vhd`, `mmu_sv39.vhd`, `mul_div.vhd`, `atomics.vhd`, `trap.vhd` — Composite modules
- `rv64gc_core.vhd` — RV64GC core
- `clint.vhd`, `plic.vhd`, `uart.vhd`, `ram.vhd`, `bootrom.vhd`, `wb_interconnect.vhd` — Peripheral stubs

## 3. GHDL Validation

### Analysis (syntax + type checking)

```bash
sh scripts/fpga/ghdl_validate_rv64.shs --analyze
```

### Elaboration (linkage verification)

```bash
sh scripts/fpga/ghdl_validate_rv64.shs --elaborate
```

### Simulation (behavioral test)

```bash
sh scripts/fpga/ghdl_validate_rv64.shs --simulate
```

The testbench (`tb_rv64_wb_soc_smoke.vhd`) drives clock at 100 MHz, asserts/deasserts reset, and monitors UART TX for output.

## 4. Vivado Synthesis

Generate the Vivado TCL script from Simple:

```bash
bin/simple run -e 'use std.hardware.fpga_linux.synthesis_wrapper.{generate_vivado_tcl_rv64}; print(generate_vivado_tcl_rv64())' > build/vhdl/rv64/synth_rv64.tcl
```

Generate XDC constraints:

```bash
bin/simple run -e 'use std.hardware.fpga_k26.k26_xdc.{k26_generate_xdc}; print(k26_generate_xdc())' > build/vhdl/rv64/k26_constraints.xdc
```

Run Vivado synthesis:

```bash
source ~/Xilinx/2025.2/Vivado/settings64.sh
cd build/vhdl/rv64
vivado -mode batch -source synth_rv64.tcl
```

## 5. FPGA Programming

Connect KV260 via USB (FTDI FT4232H — ch0=JTAG, ch1=UART).

```bash
source ~/Xilinx/2025.2/Vivado/settings64.sh
vivado -mode batch -source program.tcl
```

Or via hw_server:

```bash
open_hw_manager
connect_hw_server
open_hw_target
set_property PROGRAM.FILE {rv64gc_soc.bit} [current_hw_device]
program_hw_devices [current_hw_device]
```

## 6. UART Console

Connect to UART on the second FTDI channel:

```bash
# Using minicom
minicom -D /dev/ttyUSB1 -b 115200

# Using screen
screen /dev/ttyUSB1 115200
```

Expected output: SBI banner followed by Linux kernel boot messages.

Settings: 115200 baud, 8N1, no flow control.

## 7. Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| `ghdl -a` errors | VHDL backend codegen bug | Check `src/compiler/70.backend/backend/vhdl_*.spl` |
| `ghdl -e` fails | Missing entity/architecture | Verify all .vhd files generated in `build/vhdl/rv64/` |
| Vivado timing failure | Clock constraint mismatch | Check XDC `create_clock` period vs entity generic |
| No UART output | Wrong /dev/ttyUSB port | Try ttyUSB0-5; FTDI ch1 is typically ttyUSB1 |
| JTAG connection fails | hw_server not running | Run `hw_server` in separate terminal |
| LUT utilization >100% | RV64GC too large for K26 | Disable M-ext/A-ext or use multi-cycle datapath |

## 8. DE10-Nano (Cyclone V) Notes

**Status: Deferred** — Quartus not installed.

The DE10-Nano (5CSEBA6U23I7) is a secondary target. Requirements:
- Quartus Prime Lite 23.1+
- Separate XDC-equivalent (.qsf) pin assignments
- Different clock/reset topology (50 MHz oscillator)
- UART via GPIO header pins

Support will be added when Quartus is available.
