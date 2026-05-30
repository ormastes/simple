# KV260 RV64GC FPGA Boot Guide

End-to-end guide for generating, validating, synthesizing, and booting an RV64GC SoC on the Kria KV260 (K26 SOM, xck26-sfvc784-2LV-c).

## Current Validation Status

As of 2026-05-29, the NaxRiscv RV64 SoC bitstream has been synthesized and programmed on a physical KV260/K26 FPGA through the carrier's merged Xilinx USB JTAG interface. The same USB connection exposes FT4232H serial ports. The merged USB UART path is verified through ZynqMP PS UART1, but the loaded RV64 PL image routes its own console to PMOD pins H12/E10 rather than merged USB.

Verified on physical hardware:

- Vivado 2025.2 synthesis, implementation, timing closure, and bitstream generation — completed successfully.
- Bitstream: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` (4.3 MB, May 21 2026).
- KV260/K26 FPGA detected via Vivado hw_server as `xck26_0 arm_dap_1` on target `localhost:3121/xilinx_tcf/Xilinx/XFL1OSWWFM2BA`.
- KV260/K26 FPGA programmed via Vivado hw_server on 2026-05-29 — `End of startup status: HIGH`.
- Programming log: `build/kv260_uart_program_20260529_124641/kv260_program_20260529_124641.log`.
- BIOS rebuilt with serial UART on PMOD pins H12 (TX) / E10 (RX), LVCMOS33.
- Verilog, XDC, and CSR map verified correct for serial UART at 0xf0001000.
- OpenOCD/openFPGALoader confirmed incompatible with K26 FT4232H (proprietary Xilinx JTAG).
- Merged USB UART sampling while programming checked `/dev/ttyUSB4`, `/dev/ttyUSB5`, and `/dev/ttyUSB6` for 30 seconds at 115200 8N1. All captures were zero bytes. Artifacts: `build/kv260_uart_program_20260529_124641/`.
- Merged USB UART positive path verified with XSDB/JTAG write to ZynqMP PS UART1. The marker `KV260-PS-UART-JTAG` was captured from `/dev/ttyUSB4`. Artifacts: `build/kv260_ps_uart_jtag_probe_20260529_125214/`.

Verified in test workspace:

- RV64GC / SoC / FPGA Linux specification tests pass through `bin/simple test`.
- VHDL/RV64 generation and string-level synthesis script checks pass.
- Bounded interpreter and native test-runner probes complete without leaving `simple` child processes.
- Generated RV64 Linux handoff smoke passes in GHDL:
  `[GHDL-GEN-RV64-LINUX-HANDOFF] PASS`.
- QEMU RV64 SimpleOS logs show boot markers and HTTP bind/listen behavior when
  virtio networking is present, but this is not physical KV260 network proof.

Not yet verified:

- GHDL analysis/elaboration/simulation of the generated RV64GC SoC.
- Loading OpenSBI / Linux payloads on the generated SoC.
- Observing UART boot messages from physical FPGA hardware.
- Proving whether any FT4232H channel on this carrier can be routed to the PL UART for a future generated image. Current evidence says this image routes UART to PMOD pins H12/E10, while merged USB `/dev/ttyUSB4` is ZynqMP PS UART1.
- Physical KV260 SimpleOS network service readiness.
- Physical KV260 HTTP request/response proof from the Simple RV64 softcore.
- Physical KV260 sshd banner/login proof from the Simple RV64 softcore.

Next step: wire a 3.3V USB-UART adapter (FT232/CH340/CP2102) to PMOD J2 pins 1 (TX), 2 (RX), 5 (GND), then run `litex_term /dev/ttyUSB_adapter --speed 115200`. The merged USB serial interfaces are still worth sampling, but the current programmed image did not emit boot text there.

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
sh scripts/fpga/program_kv260_bitstream.shs
```

The helper defaults to:

- Vivado: `/home/ormastes/Xilinx/2025.2/Vivado/bin/vivado`
- Bitstream: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit`
- Output log: `build/kv260_program_YYYYMMDD_HHMMSS.log`

Override paths when needed:

```bash
VIVADO=/path/to/vivado OUT_DIR=build/my-run \
  sh scripts/fpga/program_kv260_bitstream.shs path/to/image.bit
```

Manual programming TCL equivalent:

```tcl
open_hw_manager
connect_hw_server -allow_non_jtag
open_hw_target
current_hw_device [get_hw_devices xck26_0]
set_property PROGRAM.FILE {build/build/xilinx_kv260/gateware/xilinx_kv260.bit} [current_hw_device]
program_hw_devices [current_hw_device]
close_hw_target
close_hw_manager
quit
```

Expect: `End of startup status: HIGH` confirms successful programming. Verified 2026-05-29.

### 5.1 Simple RV64 + Linux Handoff Check

Use the combined check when the goal is to load the current Simple RV64 FPGA image, validate basic board/JTAG/UART sanity, and run the generated RV64 Linux handoff smoke:

```bash
CAPTURE_SECONDS=30 LINUX_TIMEOUT=60 \
  sh scripts/fpga/check_kv260_simple_rv64_linux.shs
```

Verified result on 2026-05-29:

```text
PASS artifacts_present
PASS simple_rv64_elf_header
PASS kv260_bitstream_loaded
INFO pl_uart_on_merged_usb=no_output rc=1
PASS merged_usb_ps_uart
PASS generated_rv64_linux_handoff
PASS kv260_simple_rv64_linux_check
```

Artifacts from the verified run are in `build/kv260_simple_rv64_linux_check_20260529_230422/`. The check records:

- `simpleos_riscv64_fpga.readelf.txt` — confirms `build/os/simpleos_riscv64_fpga.elf` is ELF64 RISC-V with entry `0x80000000`.
- `program_and_uart.log` — confirms the KV260 bitstream reached `End of startup status: HIGH`.
- `ps_uart_probe.log` — confirms merged USB `/dev/ttyUSB4` receives the `KV260-PS-UART-JTAG` sanity marker from ZynqMP UART1.
- `generated_rv64_linux_handoff.log` — confirms `[GHDL-GEN-RV64-LINUX-HANDOFF] PASS`.

### 5.2 Network Verification Status

Network-dependent SimpleOS services are not fully verified on the physical
KV260 Simple RV64 FPGA target yet. The current evidence is split this way:

| Lane | Current evidence | Status |
|------|------------------|--------|
| Physical KV260 bitstream load | `End of startup status: HIGH` in Vivado log | Verified |
| Physical merged USB UART sanity | `/dev/ttyUSB4` captures `KV260-PS-UART-JTAG` from ZynqMP PS UART1 | Verified |
| Physical PL UART boot log | Current PL image routes UART to PMOD `H12/E10`; no PMOD capture artifact yet | Not verified |
| Physical Simple RV64 network | No proven network device/bridge for the softcore yet | Not verified |
| Physical HTTP server | No host HTTP response from KV260 Simple RV64 target yet | Not verified |
| Physical sshd | No banner or login from KV260 Simple RV64 target yet | Not verified |
| QEMU RV64 HTTP | Logs show `Network service ready` and HTTP bind/listen with virtio network | QEMU-only proof |
| Generated RV64 Linux handoff | GHDL handoff smoke passes | RTL-sim proof |

Existing QEMU evidence is useful as a software baseline, but it must not be
used to claim physical FPGA web or SSH readiness. Full physical verification is
tracked as
`doc/08_tracking/feature_request/kv260_simple_rv64_network_verification_2026-05-29.md`.

The required physical verification should produce all of these artifacts:

- PL UART boot log from the PMOD UART path.
- Target network readiness log from the Simple RV64 softcore.
- Host HTTP transcript proving `GET /health` and `GET /` return `200`.
- Host SSH transcript proving banner exchange and a successful login or a
  documented key-auth flow.
- A single nonzero-exit script for failures such as missing network bridge,
  deferred HTTP, sshd timeout, or QEMU-only evidence.

Use the physical evidence gate once those artifacts exist:

```bash
sh scripts/fpga/check_kv260_simple_rv64_network.shs --artifacts build/kv260-network-physical
```

The artifact directory must contain `program.log`, `pl_uart.log`,
`network.sdn`, `http_health.log`, `http_root.log`, and `ssh.log`. The gate
requires `End of startup status: HIGH`, SimpleOS RV64 PL UART boot and
`Network service ready` markers, a physical transport mapping, HTTP 200
transcripts for `/health` and `/`, and SSH banner/login proof. It exits
nonzero when only QEMU or RTL-sim evidence is available.

## 6. UART Console

The carrier's merged USB exposes the Xilinx FT4232H JTAG/UART device. On the verified host the board appears as:

```text
usb-Xilinx_ML_Carrier_Card_XFL1OSWWFM2B-if01-port0 -> /dev/ttyUSB4
usb-Xilinx_ML_Carrier_Card_XFL1OSWWFM2B-if02-port0 -> /dev/ttyUSB5
usb-Xilinx_ML_Carrier_Card_XFL1OSWWFM2B-if03-port0 -> /dev/ttyUSB6
```

Before Vivado programs or claims the JTAG interface, `if00` may also appear as a tty. After `hw_server` owns JTAG, `if00` is not normally available as a Linux serial port.

### 6.1 Merged USB PS UART

The merged USB UART path was verified independently from the PL image by writing a marker to ZynqMP PS UART1 over XSDB/JTAG while capturing all Xilinx serial ports:

```bash
sh scripts/fpga/probe_kv260_ps_uart_jtag.shs
```

Verified result on 2026-05-29:

```text
PS_UART_CAPTURE_DONE port=/dev/ttyUSB4 bytes=20
KV260-PS-UART-JTAG
PS_UART_CAPTURE_DONE port=/dev/ttyUSB5 bytes=0
PS_UART_CAPTURE_DONE port=/dev/ttyUSB6 bytes=0
UART1_SR_BEFORE=FF01002C:   00000008
UART1_SR_AFTER=FF01002C:   00000008
PS_UART_PROBE_STATUS=output_seen
```

This proves `/dev/ttyUSB4` is the active merged USB UART lane for ZynqMP PS UART1 on this host.

### 6.2 Loaded PL Image UART

Sample the merged USB UART candidates while programming, which catches early boot output that could be missed by sampling only after programming:

```bash
CAPTURE_SECONDS=30 sh scripts/fpga/program_kv260_with_uart_capture.shs
```

The helper starts readers on all `usb-Xilinx_ML_Carrier_Card_*-port0` serial ports, programs the bitstream through Vivado, then writes raw and printable captures under `build/kv260_uart_program_YYYYMMDD_HHMMSS/`.

The 2026-05-29 capture during a successful program operation reported:

```text
PROGRAM_STATUS=ok log=build/kv260_uart_program_20260529_124641/kv260_program_20260529_124641.log
INFO: [Labtools 27-3164] End of startup status: HIGH
PROGRAM_HW_DEVICES_DONE
UART_CAPTURE_DONE port=/dev/ttyUSB4 bytes=0
UART_CAPTURE_DONE port=/dev/ttyUSB5 bytes=0
UART_CAPTURE_DONE port=/dev/ttyUSB6 bytes=0
PROGRAM_CAPTURE_PROGRAM_STATUS=ok
UART_CAPTURE_STATUS=no_output
```

The generated SoC serial UART is currently constrained on PMOD pins, so use an external 3.3V USB-UART adapter for expected PL console output. The loaded bitstream's generated XDC confirms:

```tcl
set_property LOC H12 [get_ports {serial_tx}]
set_property LOC E10 [get_ports {serial_rx}]
```

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

### USB Device Mapping (KV260 ML Carrier, verified 2026-05-29)

| by-id interface | Observed tty | Current evidence |
|-----------------|--------------|------------------|
| if00 | disappears after Vivado JTAG attach | JTAG path owned by Vivado hw_server |
| if01 | `/dev/ttyUSB4` | No bytes after PL programming |
| if02 | `/dev/ttyUSB5` | No bytes after PL programming |
| if03 | `/dev/ttyUSB6` | No bytes after PL programming |

No merged USB channel has been proven to provide PL UART access for this generated image. Use the PMOD adapter path for the PL UART until the carrier routing is changed or the design is rebuilt to target a routed serial channel.

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
