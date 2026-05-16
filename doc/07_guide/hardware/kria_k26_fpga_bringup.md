# Kria K26 FPGA Bring-Up Guide

<!-- codex-research -->

This guide records the current bring-up state for the connected FPGA board and the reproducible checks for the requested UART, hello, RISC-V, SimpleOS, and web/DB path.

## Current Hardware Evidence

Host USB serial enumeration shows a Xilinx ML Carrier Card exposing FT4232H interfaces as `/dev/ttyUSB*`, with serial identity `Xilinx_ML_Carrier_Card_XFL1OSWWFM2B`.

Vivado hardware manager detects:

```text
HW_TARGETS=localhost:3121/xilinx_tcf/Xilinx/XFL1OSWWFM2BA
HW_DEVICES=xck26_0 arm_dap_1
```

Interpretation: the attached hardware is a Kria K26/Zynq UltraScale+ style target, not the earlier MLK-S02 Artix-7 path. The `examples/09_embedded/fpga_riscv/mlk_s02_100t*` files are not directly loadable to this board without a K26-specific Vivado design.

`openFPGALoader -c ft4232 --detect` can open the adapter but currently reports an empty chain. Use Vivado hardware manager as the current authoritative detection evidence.

## UART Log Check

First UART sample command:

```bash
for dev in /dev/ttyUSB0 /dev/ttyUSB1 /dev/ttyUSB2 /dev/ttyUSB3; do
  stty -F "$dev" 115200 cs8 -cstopb -parenb -ixon -ixoff raw -echo
  timeout 3s dd if="$dev" bs=1 count=256 2>/dev/null | od -An -tx1 -v
done
```

Current result: no UART bytes were observed at 115200 8N1. That is not a successful boot log.

## Web Research Summary

- AMD Kria K26 SOM is based on a custom Zynq UltraScale+ MPSoC device. Source: AMD DS987 K26 SOM data sheet, revision 1.6, 2026-03-25: `https://docs.amd.com/r/en-US/ds987-k26-som/Ordering-Information`.
- Kria starter kits use QSPI boot firmware to start U-Boot, then hand off to SD-card Linux. Source: `https://xilinx.github.io/kria-apps-docs/bootfw/build/html/docs/bootfw_overview.html`.
- AMD-designed Kria carrier cards use FTDI for USB JTAG/UART, with Vivado/XSDB detection tied to FTDI EEPROM configuration. Source: `https://xilinx.github.io/kria-apps-docs/creating_applications/2022.1/build/html/docs/FTDI_EEPROM_design_guide.html`.

## Reproducible Gate Script

Run local/simulation checks without failing the command on known missing hardware gates:

```bash
scripts/check-kria-k26-fpga-bringup.shs --local-only
```

Run the full objective gate:

```bash
scripts/check-kria-k26-fpga-bringup.shs
```

Full mode exits nonzero until the physical RV64 bitstream, SimpleOS boot, and board web-server gates are real.

Current local-only evidence:

```text
FAIL uart_boot_log_detected
FAIL openfpgaloader_chain_detected_empty
PASS vivado_kria_k26_detected
PASS simple_hello_world
PASS riscv_fpga_ghdl_hello
PASS web_stack_db_persistence_spec
PASS web_stack_source_contract_spec
FAIL physical_rv64_bitstream_loaded
FAIL simpleos_started_on_fpga
FAIL board_web_server_with_db_responded
```

## Bootstrap Status

Simple hello world passes on the host:

```bash
bin/simple run examples/01_getting_started/hello_native.spl
```

Observed output:

```text
Hello World
```

The current repo FPGA RISC-V hello lane passes in GHDL simulation using `examples/09_embedded/baremetal/baremetal/hello_riscv32_semihost.s` and `src/lib/nogc_async_mut_noalloc/baremetal/ghdl_runner.shs`.

This proves the simulation lane only. It does not prove a RISC-V core is running on the K26.

## SimpleOS and RV64 Status

The requested "load Simple-made RISC-V 64 and load SimpleOS" path is not currently achievable on this hardware with checked-in artifacts.

Missing hardware work:

- K26-specific Vivado top for the RV64 core in programmable logic.
- Clock/reset/UART/timer/memory integration.
- ELF or boot-image loader path.
- UART-confirmed RV64 hello on the board.
- SimpleOS boot image and startup proof on that RV64 system.

## Web Server With DB Status

The DB-backed app surface is verified by tests:

```bash
bin/simple test test/integration/app/web_stack_sample_persistence_spec.spl --mode=interpreter
bin/simple test test/integration/app/web_stack_sample_spec.spl --mode=interpreter
```

Current result:

- persistence spec: 1 example, 0 failures
- source contract spec: 4 examples, 0 failures

The example runner path still times out under the examples timeout guard, and the board web server has not been opened.

## Completion Checklist

- UART boot log: missing.
- FPGA connection identity: verified as K26 through Vivado.
- Web research: done, with AMD/Xilinx sources listed above.
- Guide doc: this file.
- Hello world bootstrap: host Simple and GHDL RISC-V simulation pass.
- Simple-made RV64 load: missing K26 hardware design.
- SimpleOS load/start: missing RV64 hardware boot path.
- Web server with DB: DB behavior verified in tests; live board server missing.
