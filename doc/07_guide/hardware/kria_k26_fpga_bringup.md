# Kria K26 FPGA Bring-Up Guide

Hands-on guide for building and flashing a NaxRiscv RV64 SoC on the Kria K26 (XCZU5EV) using LiteX and Vivado. Based on actual bringup experience — 2026-05-20.

## Hardware Setup

| Component | Detail |
|-----------|--------|
| SOM | Kria K26 (xck26-sfvc784-2lv-c), Zynq UltraScale+ MPSoC |
| Carrier | KV260 ML Carrier Card (Vision AI Starter Kit) |
| USB bridge | FT4232H (VID 0x0403, PID 0x6011), serial `XFL1OSWWFM2BA` |
| JTAG target | `localhost:3121/xilinx_tcf/Xilinx/XFL1OSWWFM2BA` |
| Detected devices | `xck26_0` (FPGA) + `arm_dap_1` (ARM DAP) |

### FT4232H Channel Map

| Channel | ttyUSB | Function | Notes |
|---------|--------|----------|-------|
| A (ADBUS) | ttyUSB0 | JTAG | Vivado hw_server uses this; openocd/openFPGALoader cannot |
| B (BDBUS) | ttyUSB2 | PS UART1 (MIO 36-37) | Only active with PMUFW/FSBL running on A53 |
| C (CDBUS) | ttyUSB3 | **Not routed to PL** | Carrier board XML confirms no PL UART interface |
| D (DDBUS) | ttyUSB5 | Spare | Not connected to PL pins |

**Key finding:** The KV260 carrier card does NOT route FT4232H Ch.C/D to PL FPGA pins. The carrier board.xml only defines PS fixedio, I2C, and MIPI CSI interfaces. There is no on-board PL serial UART path.

## Prerequisites

### 1. Vivado Device Family Installation

The K26 requires the **Zynq UltraScale+ MPSoC** device family. The default Vivado install (Artix-7 only) cannot synthesize for this part.

```bash
# Generate auth token (requires interactive TTY — Java System.console())
python3 -c "import pty; pty.spawn(['/home/ormastes/Xilinx/.xinstall/2025.2/xsetup', '-b', 'AuthTokenGen'])"
```

Write installer config — the exact module names are critical:

```ini
# /tmp/vivado_add_zynquplus.txt
Edition=Vivado ML Standard
Product=Vivado
Destination=/home/ormastes/Xilinx/2025.2
Modules=Zynq UltraScale+ MPSoCs:1,Install Devices for Kria SOMs and Starter Kits:1
```

**Pitfall:** The module name is `Zynq UltraScale+ MPSoCs` (plural "s"), NOT `MPSoC`. The installer silently ignores wrong names without error. Correct names were discovered by grepping Vivado install logs.

```bash
/home/ormastes/Xilinx/.xinstall/2025.2/xsetup \
  -b Install \
  -a XilinxEULA,3rdPartyEULA \
  -c /tmp/vivado_add_zynquplus.txt
```

Download is ~14.16 GB. Verify installation:

```bash
cat /home/ormastes/Xilinx/2025.2/data/installed.devices | python3 -m json.tool | grep -A1 zynquplus
# Should show: "name": "zynquplus-family" with xck26 in the devices list
```

### 2. LiteX Environment

```bash
cd build
python3 -m venv litex-venv
source litex-venv/bin/activate
pip install meson meson-python litex litex-boards pythondata-cpu-naxriscv
```

NaxRiscv requires Java 8 (SpinalHDL) and sbt:

```bash
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH="$JAVA_HOME/bin:$HOME/.local/sbt/bin:$PATH"
```

### 3. USB Permissions

```bash
# /etc/udev/rules.d/99-ft4232h-jtag.rules
SUBSYSTEM=="usb", ATTRS{idVendor}=="0403", ATTRS{idProduct}=="6011", MODE="0666", GROUP="plugdev"
```

```bash
sudo udevadm control --reload-rules && sudo udevadm trigger
```

## SoC Architecture

The K26 has no PL clock source — PS must provide FCLK_CLK0. Architecture:

```
┌─────────────────────────────────────────────┐
│  Zynq UltraScale+ PS (clock-only mode)      │
│  ├─ FCLK_CLK0 = 100 MHz → PL sys_clk       │
│  ├─ pl_resetn0 → PL sys_rst                 │
│  └─ UART1 on MIO 36-37 (PS console, unused) │
├─────────────────────────────────────────────┤
│  PL Fabric                                   │
│  ├─ NaxRiscv RV64GC CPU                      │
│  ├─ 64 KB integrated SRAM                    │
│  ├─ JTAG UART (via BSCANE2)                  │
│  ├─ Timer                                    │
│  └─ LiteX BIOS in SRAM                       │
└─────────────────────────────────────────────┘
```

Target file: `build/k26_naxriscv_rv64.py` (174 lines)

## Build

```bash
source build/litex-venv/bin/activate
source /home/ormastes/Xilinx/2025.2/Vivado/settings64.sh
export JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64
export PATH="$JAVA_HOME/bin:$HOME/.local/sbt/bin:$PATH"

cd build
python3 k26_naxriscv_rv64.py --build --xlen 64
```

This runs Vivado synthesis + implementation + bitstream generation. Takes ~15-20 minutes. Output: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` (~4.1 MB).

## Flash via Vivado hw_server

openFPGALoader and openocd cannot communicate with the K26 JTAG chain on this carrier card — the FT4232H JTAG pin mapping is proprietary to Xilinx. Use Vivado hw_server exclusively.

### Start hw_server

```bash
source /home/ormastes/Xilinx/2025.2/Vivado/settings64.sh
hw_server &
```

### Program via TCL batch

```tcl
# /tmp/program_k26.tcl
open_hw_manager
connect_hw_server -url localhost:3121
open_hw_target
current_hw_device [get_hw_devices xck26_0]
set_property PROGRAM.FILE {build/build/xilinx_kv260/gateware/xilinx_kv260.bit} [current_hw_device]
puts "=== Programming xck26_0 ==="
program_hw_devices [current_hw_device]
puts "=== Programming complete! ==="
close_hw_target
close_hw_manager
quit
```

```bash
vivado -mode batch -source /tmp/program_k26.tcl
```

Expect: `End of startup status: HIGH` confirms successful programming.

## UART Console — Current Status and Options

The SoC uses JTAG UART (BSCANE2-based), which requires openocd to stream data. Since openocd cannot talk to the K26 JTAG chain via this carrier's FT4232H, the console is not yet accessible.

### Option A: Vivado XVC Bridge (no extra hardware)

Use Vivado's hw_server as a JTAG transport, exposing XVC (Xilinx Virtual Cable) for openocd:

```bash
hw_server -e "set xvc-server enable 1"
```

Then configure openocd to use the XVC interface instead of raw FTDI. litex_term connects through that openocd instance.

### Option B: PMOD Serial UART (requires USB-UART adapter)

Rebuild SoC with `uart_name="serial"` and route TX/RX through PMOD header pins:

| Signal | PMOD Pin | SOM240 Pin | FPGA Loc | IOStandard |
|--------|----------|------------|----------|------------|
| TX | 1 (HDA11) | som240_1_d18 | H12 | LVCMOS33 |
| RX | 2 (HDA12) | som240_1_d20 | E10 | LVCMOS33 |

Wire a USB-UART adapter (FT232/CH340/CP2102) to PMOD pins 1, 2, and GND (pin 5). Then: `litex_term /dev/ttyUSB_adapter --speed 115200`.

## openocd / openFPGALoader — Why They Fail

| Tool | Error | Root Cause |
|------|-------|------------|
| openFPGALoader | Empty JTAG chain | Wrong channel/pin mapping for this carrier |
| openocd | "all ones" (0xFFFFFFFF) | `ftdi_layout_init` bit positions don't match Kria FT4232H wiring |

The KV260 ML carrier uses a non-standard FT4232H JTAG pin mapping. ADBUS[4] is a level-shifter output-enable, not nTRST. Vivado hw_server knows the correct mapping via FTDI EEPROM metadata.

## Simple RISC-V RTL and VHDL Generation

The repo contains RV32I RTL written in Simple language (64 .spl files) with a VHDL backend:

```bash
# Generate VHDL from Simple RTL (requires @hardware annotation)
bin/simple compile --backend=vhdl src/lib/hardware/rv32i/alu.spl
```

Generated VHDL files in `build/vhdl-output/`:

| File | Size | Content |
|------|------|---------|
| `rv32i_alu.vhd` | 5.0 KB | 10 ALU operation entities |
| `rv32i_regfile.vhd` | 1.5 KB | 32x32 register file (2R1W, x0=0) |
| `rv32i_pkg.vhd` | 3.2 KB | RV32I opcode constants |
| `rv32i_field_extractor.vhd` | 1.8 KB | Instruction field decoder |
| `rv32i_alu_control.vhd` | 2.5 KB | ALU control decoder |
| `rv32i_decode_pkg.vhd` | 3.2 KB | Decode constants package |

## References

- AMD K26 SOM data sheet (DS987): ordering, electrical, thermal
- AMD KV260 User Guide (UG1089): carrier card schematic, connector pinout
- AMD Kria boot firmware overview: QSPI→U-Boot→SD card boot flow
- AMD FTDI EEPROM design guide: explains hw_server JTAG detection
- LiteX KV260 upstream target: `litex_boards/targets/xilinx_kv260.py` (uses zynqmp CPU, no_uart=True)

## Completion Status

- [x] Vivado Zynq UltraScale+ device family installed (14.16 GB)
- [x] K26 detected via Vivado hw_server (`xck26_0` + `arm_dap_1`)
- [x] LiteX SoC target created (`build/k26_naxriscv_rv64.py`)
- [x] NaxRiscv RV64 bitstream built (4.1 MB, 0 errors)
- [x] FPGA programmed via Vivado TCL batch
- [x] Simple RV32I → VHDL generation verified (6 files, ~17 KB)
- [ ] UART console connected (blocked: openocd incompatibility, XVC bridge or PMOD path needed)
- [ ] LiteX BIOS boot message observed
- [ ] SimpleOS boot on RV64
