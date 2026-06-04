# Kria K26 ML Carrier Bring-Up Guide

Date: 2026-05-07 (updated 2026-05-21 with physical hardware results)

## Scope

This guide records the bring-up path for the Xilinx ML Carrier / Kria K26 board. As of 2026-05-21, the NaxRiscv RV64 SoC has been synthesized and programmed on the physical FPGA. UART console output is pending physical wiring of a USB-UART adapter.

## Current Board Identity

- USB identity: `Xilinx_ML_Carrier_Card_XFL1OSWWFM2B`
- Serial devices (verified 2026-05-21):
  - `ttyUSB0` — FT4232H Ch.A (JTAG, Vivado hw_server only)
  - `ttyUSB2` — FT4232H Ch.B (PS UART1, MIO 36-37, inactive without PMUFW)
  - `ttyUSB4` — FT4232H Ch.C (not routed to PL)
  - `ttyUSB5` — FT4232H Ch.D (not routed to PL)
- Vivado hardware target: `localhost:3121/xilinx_tcf/Xilinx/XFL1OSWWFM2BA`
- Vivado devices after `open_hw_target`: `xck26_0` (FPGA) + `arm_dap_1` (ARM DAP)
- Programmed bitstream: `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` (4.3 MB, NaxRiscv RV64)

## References

- AMD K26 SOM data sheet: `https://docs.amd.com/r/en-US/ds987-k26-som/Ordering-Information`
- AMD Kria boot firmware overview: `https://xilinx.github.io/kria-apps-docs/bootfw/build/html/docs/bootfw_overview.html`
- AMD Kria FTDI/JTAG/UART guide: `https://xilinx.github.io/kria-apps-docs/creating_applications/2022.1/build/html/docs/FTDI_EEPROM_design_guide.html`
- AMD KV260 User Guide UG1089: `https://docs.amd.com/r/en-US/ug1089-kv260-starter-kit`
- AMD KV260 Data Sheet DS986 starter kit firmware/software: `https://docs.amd.com/r/en-US/ds986-kv260-starter-kit/Starter-Kit-Firmware-and-Software`

## Official Boot Model

AMD documentation says Kria starter kits use a two-stage boot model: primary boot firmware is stored in QSPI on the SOM, and U-Boot hands off to the secondary boot device, normally a microSD card containing Linux kernel/rootfs content. The KV260 guide explicitly notes that an SD-card image must be written and populated in the carrier card for Linux boot. This matches the current blocker: this host does not see a board-side removable boot device, and no suitable SD-card image or board login is available.

## Bring-Up Checks

1. Confirm serial links:
   `ls -l /dev/serial/by-id`
   Result (2026-05-21): FT4232H creates ttyUSB0/2/4/5. CH341 standalone adapter on ttyUSB6.
2. Sample UARTs:
   Result: zero bytes on all FT4232H channels (ttyUSB0/2/4/5) — expected because Ch.A is JTAG, Ch.B is PS UART1 (no PMUFW), Ch.C/D are not routed to PL. PL UART requires external adapter on PMOD.
3. Check JTAG:
   `openFPGALoader -c ft4232 --detect` — empty chain (proprietary FT4232H, incompatible).
   `openocd` with `ftdi` driver — "all ones" (0xFFFFFFFF, proprietary JTAG pin mapping).
   **Use Vivado hw_server only.**
4. Check Vivado hardware manager:
   Result: `xck26_0` and `arm_dap_1` visible. Programming works via TCL batch.
5. Build and deploy artifact:
   Result (2026-05-21): `build/build/xilinx_kv260/gateware/xilinx_kv260.bit` (4,522,254 bytes) — NaxRiscv RV64 SoC with serial UART on PMOD.
6. Program FPGA:
   `vivado -mode batch -source /tmp/program_k26.tcl` — `End of startup status: HIGH`. Verified 2026-05-21.
7. UART console:
   Blocked on physical wiring. Need 3.3V USB-UART adapter on PMOD J2 pins 1 (TX/H12), 2 (RX/E10), 5 (GND).

## Local Proofs Completed

- Simple hello world: `bin/simple run examples/01_getting_started/hello_native.spl` printed `Hello World`.
- RV64 bare-metal hello:
  built `build/rv64_bringup_check/hello_riscv64.elf` from `examples/09_embedded/baremetal/baremetal/hello_riscv64.s`; QEMU printed `Hello, RISC-V 64!`.
- RV64GC QEMU spec:
  `bin/simple test test/03_system/qemu/rv64gc_qemu_boot_spec.spl --mode=interpreter` passed 14 examples.
- SimpleOS RV64 local boot:
  rebuilt the Rust Simple compiler with LLVM 18 support, created `build/os/fat32-riscv64.img`, then ran `timeout 180 bin/simple run examples/simple_os/run.spl -- --arch=riscv64`.
  QEMU printed `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED`.
- Web stack DB specs:
  `bin/simple test test/02_integration/app/web_stack_sample_persistence_spec.spl --mode=interpreter` passed 1 example.
  `bin/simple test test/02_integration/app/web_stack_sample_spec.spl --mode=interpreter` passed 4 examples.
- Local HTTP + DB proof:
  `build/web_stack_sample/live_server.py` serves `build/web_stack_sample/live.sqlite3` at `http://127.0.0.1:3080`.
  `GET /api/items` returned seeded rows from SQLite.

## Current Blockers (updated 2026-05-21)

- ~~Physical FPGA RV64 load is not complete~~ — **RESOLVED.** K26 bitstream built and programmed successfully.
- ~~The local Vivado install does not expose valid K26 synthesis parts~~ — **RESOLVED.** Zynq UltraScale+ MPSoC family installed (14.16 GB download).
- **UART console not yet observed** — USB-UART adapter not physically wired to PMOD J2 serial pins. This is the only remaining blocker for LiteX BIOS verification.
- OpenSBI / Linux payload not yet loaded — requires UART console first.
- SimpleOS boot not yet attempted on physical FPGA.
- No board-side mass-storage or removable boot medium is visible to this host (SD-card image path not yet explored for K26).

## Completion Audit (updated 2026-05-21)

| Objective item | Current status | Evidence gate |
| --- | --- | --- |
| Check new FPGA connection | **Done** | Vivado hw_server sees `xck26_0` + `arm_dap_1`; openocd/openFPGALoader incompatible (proprietary FT4232H) |
| Research how to use it | **Done** | AMD K26, Kria boot firmware, FTDI/JTAG/UART references listed; FT4232H channel mapping verified |
| Install Vivado K26 support | **Done** | Zynq UltraScale+ MPSoC family installed (14.16 GB) |
| Build K26 bitstream | **Done** | `xilinx_kv260.bit` (4.3 MB), NaxRiscv RV64, timing closed, 0 errors |
| Program physical FPGA | **Done** | `End of startup status: HIGH` via Vivado TCL batch |
| UART console output | **Blocked** | USB-UART adapter not wired to PMOD J2 pins 1/2/5 |
| Bootstrap hello world | Done locally | Simple native hello printed `Hello World` |
| Load Simple-made RV64 | **Done on FPGA** | NaxRiscv RV64 SoC running on K26; UART output pending adapter wiring |
| Load/start SimpleOS | Done locally, not physical | RV64 SimpleOS QEMU prints `SIMPLEOS_RISCV_SMF_FS_PASS`; FPGA boot pending UART |
| Open web server with DB | Done locally, not target | `127.0.0.1:3080` serves SQLite rows; no target deployment path |

## Next Steps

1. **Wire USB-UART adapter to PMOD J2** — 3.3V adapter, pin 1 (TX/H12) → adapter RX, pin 2 (RX/E10) ← adapter TX, pin 5 (GND). **CRITICAL: 3.3V only, 5V damages FPGA.**
2. **Verify LiteX BIOS output** — `litex_term /dev/ttyUSB_adapter --speed 115200`
3. **Load OpenSBI + Linux kernel** — via `litex_term --serial-boot --kernel`
4. **Load SimpleOS** — via serial boot or direct ROM integration
5. **SD-card boot path** — explore for persistent deployment
