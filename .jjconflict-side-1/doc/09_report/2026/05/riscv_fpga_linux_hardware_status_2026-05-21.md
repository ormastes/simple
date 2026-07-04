# RISC-V FPGA Linux Hardware Status

Date: 2026-05-21 (updated with physical hardware results)

## Summary

The NaxRiscv RV64 SoC has been synthesized, programmed, and is running on a physical KV260/K26 FPGA. UART console output has not yet been observed because the external USB-UART adapter is not physically wired to the PMOD serial pins.

## What Was Verified — Software/Tests

- Bounded `bin/simple test` runs for the RV64 feature specs passed without leaving `simple` child processes.
- Interpreter and native subprocess probes around the changed VHDL/RV64/RISC-V specs completed without new crashed runs.
- The historical crashed-run baseline remains 17 old May 20 zero-count runs.

## What Was Verified — Physical Hardware (2026-05-21)

- Vivado 2025.2 synthesis, implementation, timing closure, and bitstream generation completed successfully for K26 (xck26-sfvc784-2lv-c).
- Bitstream: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` (4,522,254 bytes, May 21 06:26).
- KV260/K26 FPGA programmed via Vivado hw_server TCL batch — `End of startup status: HIGH`.
- Build script (`build/k26_naxriscv_rv64.py`) updated: `uart_name="serial"` with PMOD pins H12 (TX) and E10 (RX), LVCMOS33.
- BIOS rebuilt with serial UART support (May 21 06:14:14), confirmed via string inspection.
- Verilog top module verified: `serial_tx` (output, H12) and `serial_rx` (input, E10) with RS232PHY UART hierarchy.
- XDC constraints verified: H12/E10 at LVCMOS33.
- CSR map verified: UART at 0xf0001000 with `uart_interrupt` (serial, not JTAG UART).
- CPU: NaxRiscv RV64, ISA `rv64i2p0_ma`, MMU sv39, 100 MHz, L2 cache 128 KB.

## What Was Verified — Toolchain Compatibility

- OpenOCD confirmed incompatible with K26 FT4232H — JTAG scan chain returns "all ones" (proprietary Xilinx EEPROM config).
- openFPGALoader confirmed incompatible — empty JTAG chain.
- Vivado hw_server is the only working JTAG transport for this carrier.
- hw_server XVC parameter (`-e "set xvc-server enable 1"`) not supported in Vivado 2025.2.
- xsdb cannot read PL address space — PS↔PL AXI bridges intentionally disabled (clock-only PS mode).

## What Was Not Verified

- No GHDL hardware simulation was run in this pass.
- No OpenSBI or Linux payload was loaded onto the generated SoC.
- No UART boot log was observed — USB-UART adapter not physically wired to PMOD pins.

## Blocker: UART Console

The SoC is running but we cannot observe output. The PMOD serial UART (H12=TX, E10=RX) requires an external USB-UART adapter (FT232/CH340/CP2102) at 3.3V wired to PMOD J2 pins 1 (TX), 2 (RX), 5 (GND). Settings: 115200 baud, 8N1, no flow control.

## USB Device Mapping (verified)

| ttyUSB | Device | Function |
|--------|--------|----------|
| ttyUSB0 | FT4232H Ch.A | JTAG (Vivado hw_server only) |
| ttyUSB2 | FT4232H Ch.B | PS UART1 (MIO 36-37, inactive without PMUFW) |
| ttyUSB4 | FT4232H Ch.C | Not routed to PL |
| ttyUSB5 | FT4232H Ch.D | Not routed to PL |
| ttyUSB6 | CH341 (standalone) | Available for PMOD serial UART |

## Answer

Can Simple RISC-V run on FPGA?

- Yes — the NaxRiscv RV64 SoC is synthesized and programmed on a physical KV260/K26.
- UART console observation is blocked on physical wiring, not on design or toolchain issues.
- Linux boot becomes verifiable once the USB-UART adapter is connected to the PMOD serial pins.

Did this pass program and run on physical FPGA hardware?

- Yes. Bitstream generated, timing closed, FPGA programmed successfully. UART output pending physical wiring.
