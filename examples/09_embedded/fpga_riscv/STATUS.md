# FPGA RISC-V CPU Project — Status Report
**Date:** 2026-03-23
**Target:** ZedBoard (Zynq-7020, XC7Z020-CLG484)

## Hardware Setup

### Detected Devices
| Device | USB ID | Status |
|--------|--------|--------|
| Xilinx Platform Cable USB II | `03fd:0008` | Firmware loaded, JTAG active |
| Lauterbach Power Debug II | `0897:0002` | Connected (alternate debug path) |
| WCH-Link (RISC-V probe) | `1a86:8010` | Connected |
| ST-LINK/V2.1 | `0483:374b` | Connected (ttyACM0-1) |
| STLINK-V3 | `0483:374e` | Connected (ttyACM2) |

### Platform Cable USB II
- **Problem:** Device arrived in pre-firmware state (`03fd:0013`)
- **Solution:** Loaded `xusbdfwu.hex` firmware via `fxload` from [gabrieldurante/xilinx-xusb](https://github.com/gabrieldurante/xilinx-xusb)
- **Result:** Device re-enumerated as `03fd:0008` (Platform Cable USB II active)
- **Firmware command:** `fxload -t fx2lp -I /tmp/xilinx-xusb/xusbdfwu.hex -D /dev/bus/usb/001/XXX`
- **Note:** Firmware must be reloaded after every USB replug

### JTAG Connection
- Cable firmware: OK (v0x0406, CPLD v0x200D)
- JTAG chain detection: **No target found** — ZedBoard needs power cycle or JTAG cable to J15
- Tools verified: `xc3sprog`, `urjtag`, `openFPGALoader`, `openocd` all installed

## RV32I CPU Design

### Architecture
- **ISA:** RV32I (base integer, single-cycle)
- **Features:** Full ALU, branch unit, register file (32x32), instruction decoder
- **Memory:** 4KB IMEM + 4KB DMEM (block RAM)
- **I/O:** Memory-mapped at `0x80000000` (LEDs, switches, buttons)
- **Clock:** 100 MHz (ZedBoard GCLK)
- **Reset:** Center button (BTNC)

### Files (all GHDL-validated, VHDL-2008)
| File | Lines | Description |
|------|-------|-------------|
| `rtl/rv32i_pkg.vhd` | 36 | Opcodes, ALU ops, branch types |
| `rtl/regfile.vhd` | 42 | 32x32 register file, x0=0 |
| `rtl/alu.vhd` | 46 | ADD/SUB/SLL/SLT/SLTU/XOR/SRL/SRA/OR/AND/PASS |
| `rtl/decoder.vhd` | 118 | I/R/S/B/U/J decode, immediate gen, control signals |
| `rtl/rv32i_core.vhd` | 155 | Single-cycle datapath, PC, branch eval |
| `rtl/zedboard_top.vhd` | 134 | Top wrapper, BRAM, MMIO, test program |
| `constraints/zedboard.xdc` | 58 | ZedBoard pin assignments |
| `build.tcl` | 40 | Vivado batch synthesis script |
| `program.tcl` | 22 | Vivado batch programming script |

### Test Program (embedded in IMEM)
Reads DIP switches → adds to counter → displays on LEDs → delay loop → repeat.

### Validation
```
$ ghdl -a --std=08 rtl/*.vhd   # All 6 files: OK
$ ghdl -e --std=08 zedboard_top # Elaboration: OK
```

## Tools Installed
| Tool | Version | Purpose |
|------|---------|---------|
| GHDL | 4.1.0 | VHDL analysis, elaboration, simulation |
| openFPGALoader | 0.12.0 | Universal FPGA programmer |
| OpenOCD | 0.12.0 | JTAG debugger |
| urjtag | 0.10 | JTAG chain detection |
| xc3sprog | r774 | Xilinx FPGA programmer (built from source) |
| fxload | 0.0.20081013 | USB firmware loader |

## Remaining Steps

### Immediate (once ZedBoard is powered + JTAG detected)
1. **Verify JTAG:** `detectchain -c xpc` → should show XC7Z020
2. **Reload firmware if needed:** `fxload -t fx2lp -I /tmp/xilinx-xusb/xusbdfwu.hex -D /dev/bus/usb/001/XXX`

### Synthesis (requires Vivado — not yet installed)
Vivado Lab Edition (free) needed for Xilinx 7-series synthesis. Download requires AMD account login at https://www.xilinx.com/support/download.html.

```bash
cd examples/09_embedded/fpga_riscv
vivado -mode batch -source build.tcl     # Synthesize (~5-10 min)
vivado -mode batch -source program.tcl   # Flash (~10 sec)
```

### Alternative: xpcu-xvcd + remote Vivado
If Vivado is on another machine, use `xpcu-xvcd` as a virtual cable server:
```bash
cd /tmp/xpcu-xvcd && make && ./xvcd  # Starts XVC server on port 2542
# Then from remote Vivado: connect to XVC at <this-ip>:2542
```

## Project Location
```
examples/09_embedded/fpga_riscv/
├── build.tcl, program.tcl
├── constraints/zedboard.xdc
├── rtl/{rv32i_pkg,regfile,alu,decoder,rv32i_core,zedboard_top}.vhd
└── STATUS.md (this file)
```
