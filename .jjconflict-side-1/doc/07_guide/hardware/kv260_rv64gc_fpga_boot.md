# KV260 RV64GC FPGA Boot Guide

End-to-end guide for generating, validating, synthesizing, and booting an RV64GC SoC on the Kria KV260 (K26 SOM, xck26-sfvc784-2LV-c).

## Current Validation Status

As of 2026-05-21, the NaxRiscv RV64 SoC has been synthesized, programmed, and is running on a physical KV260/K26 FPGA. UART console output is pending physical wiring of a USB-UART adapter to the PMOD serial pins.

Verified on physical hardware:

- Vivado 2025.2 synthesis, implementation, timing closure, and bitstream generation — completed successfully.
- Bitstream: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` (4.3 MB, May 21 2026).
- KV260/K26 FPGA programmed via Vivado hw_server — `End of startup status: HIGH`.
- BIOS rebuilt with serial UART on PMOD pins H12 (TX) / E10 (RX), LVCMOS33.
- Verilog, XDC, and CSR map verified correct for serial UART at 0xf0001000.
- OpenOCD/openFPGALoader confirmed incompatible with K26 FT4232H (proprietary Xilinx JTAG).

Verified in test workspace:

- RV64GC / SoC / FPGA Linux specification tests pass through `bin/simple test`.
- VHDL/RV64 generation and string-level synthesis script checks pass.
- Bounded interpreter and native test-runner probes complete without leaving `simple` child processes.

Not yet verified:

- GHDL analysis/elaboration/simulation of the generated RV64GC SoC.
- Loading OpenSBI / Linux payloads on the generated SoC.
- Observing UART boot messages from physical FPGA hardware (blocked on USB-UART adapter wiring to PMOD).

Next step: wire a 3.3V USB-UART adapter (FT232/CH340/CP2102) to PMOD J2 pins 1 (TX), 2 (RX), 5 (GND), then run `litex_term /dev/ttyUSB_adapter --speed 115200`.

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

Connect KV260 via USB (FTDI FT4232H — ch0=JTAG). Only Vivado hw_server works; openocd/openFPGALoader are incompatible with this carrier's proprietary FT4232H JTAG.

```bash
source ~/Xilinx/2025.2/Vivado/settings64.sh
hw_server &  # if not already running
vivado -mode batch -source /tmp/program_k26.tcl
```

Programming TCL script (`/tmp/program_k26.tcl`):

```tcl
open_hw_manager
connect_hw_server -url localhost:3121
open_hw_target
current_hw_device [get_hw_devices xck26_0]
set_property PROGRAM.FILE {build/build/xilinx_kv260/gateware/xilinx_kv260.bit} [current_hw_device]
program_hw_devices [current_hw_device]
close_hw_target
close_hw_manager
quit
```

Expect: `End of startup status: HIGH` confirms successful programming. Verified 2026-05-21.

## 6. UART Console

The SoC uses serial UART on PMOD pins (not FT4232H channels — those are PS-only or not routed to PL).

Wire a 3.3V USB-UART adapter (FT232/CH340/CP2102) to PMOD J2:

| Signal | PMOD Pin | FPGA Loc | Adapter Pin | IOStandard |
|--------|----------|----------|-------------|------------|
| TX | 1 (HDA11) | H12 | adapter RX | LVCMOS33 |
| RX | 2 (HDA12) | E10 | adapter TX | LVCMOS33 |
| GND | 5 | — | adapter GND | — |

**CRITICAL:** Use 3.3V adapter or 3.3V jumper setting. 5V TTL will damage the FPGA HD-bank I/O.

```bash
# Using litex_term (recommended)
litex_term /dev/ttyUSB_adapter --speed 115200

# Using minicom
minicom -D /dev/ttyUSB_adapter -b 115200

# Using screen
screen /dev/ttyUSB_adapter 115200
```

Settings: 115200 baud, 8N1, no flow control.

Target output: LiteX BIOS banner, then serialboot prompt. Linux boot requires OpenSBI + kernel payload.

### USB Device Mapping (KV260 ML Carrier, verified 2026-05-21)

| ttyUSB | Device | Function |
|--------|--------|----------|
| ttyUSB0 | FT4232H Ch.A | JTAG (Vivado hw_server only) |
| ttyUSB2 | FT4232H Ch.B | PS UART1 (MIO 36-37, inactive without PMUFW) |
| ttyUSB4 | FT4232H Ch.C | Not routed to PL |
| ttyUSB5 | FT4232H Ch.D | Not routed to PL |

None of the FT4232H channels provide PL UART access — an external adapter on the PMOD is required.

## 7. Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| `ghdl -a` errors | VHDL backend codegen bug | Check `src/compiler/70.backend/backend/vhdl_*.spl` |
| `ghdl -e` fails | Missing entity/architecture | Verify all .vhd files generated in `build/vhdl/rv64/` |
| Vivado timing failure | Clock constraint mismatch | Check XDC `create_clock` period vs entity generic |
| No UART output | Adapter not wired to PMOD | Wire 3.3V USB-UART to PMOD J2 pins 1, 2, 5 (see Section 6) |
| No UART output | TX/RX not crossed | FPGA TX (H12) must go to adapter RX, and vice versa |
| No UART output | 5V adapter | Use 3.3V — 5V damages FPGA I/O |
| JTAG fails | hw_server not running | `hw_server &` then connect to `localhost:3121` |
| openocd "all ones" | Proprietary FT4232H JTAG | Use Vivado hw_server only; openocd is incompatible |
| xsdb can't read PL | PS↔PL AXI disabled | Clock-only PS; no debug path from A53 to NaxRiscv bus |
| LUT utilization >100% | RV64GC too large for K26 | Disable M-ext/A-ext or use multi-cycle datapath |

## 8. DE10-Nano (Cyclone V) Notes

**Status: Deferred** — Quartus not installed.

The DE10-Nano (5CSEBA6U23I7) is a secondary target. Requirements:
- Quartus Prime Lite 23.1+
- Separate XDC-equivalent (.qsf) pin assignments
- Different clock/reset topology (50 MHz oscillator)
- UART via GPIO header pins

Support will be added when Quartus is available.
