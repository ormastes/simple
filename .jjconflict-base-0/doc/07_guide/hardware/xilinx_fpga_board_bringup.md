# Xilinx FPGA Board Bring-Up Guide

This guide defines the minimum work required before claiming a new Xilinx FPGA board is supported in this repo.

## Current Boundary

- The repo-native FPGA orchestration layer in `src/hardware/fpga_linux/` is real, and MLK-S02-100T board wrapper/products now exist for both `mlk_s02_100t_rv32_linux` and `mlk_s02_100t_rv64_linux`.
- The concrete handwritten Vivado wrapper under `examples/09_embedded/fpga_riscv/` is ZedBoard-specific.
- `MLK-S02-100T` is the first concrete generated-board target, but it is still not a fully verified build/program/run target in this repo until local authoritative constraints, exact part/vendor files, and hardware programming evidence are in place.

## Exact Board First

Do not start from "Artix-7 100T" alone. That identifies the FPGA family and size, not the board wiring.

Examples:
- `MLK-S02-100T`
- `Arty A7-100T`
- `Nexys A7-100T`

Those boards differ in:
- clock source and frequency
- reset polarity and reset button wiring
- UART pins and USB-UART path
- LED and switch pin mapping
- external memory type and address map

## Required Repo Changes

1. Keep the concrete board profile in `src/hardware/fpga_linux/riscv_fpga_linux.spl` aligned with the real board.
2. Confirm the committed part selection matches the exact MLK-S02-100T variant in use.
3. Replace any scaffold XDC content with locally authoritative clock, reset, UART, and memory pin assignments.
4. Keep the Vivado build path pointed at the correct generated top module and constraint file.
5. Keep the programming path aligned with the expected hardware target and lab tooling.
6. Update docs so the board name is explicit everywhere support is claimed.
7. Keep `config/resources/boards/mlk_s02_100t.sdn` and vendor acquisition notes synchronized with reality.

## Minimum Verification

Software-side preparation alone is not enough. A new board is not "working" until these levels are complete:

1. Contract validation passes.
2. RTL generation or handwritten RTL build materializes for the selected board.
3. Vivado synthesis passes for the concrete part.
4. Implementation and bitstream generation pass.
5. Hardware programming succeeds on the real board.
6. A real execution proof exists, such as UART boot markers, semihost output, MMIO result, or register readback.

## First Physical Check

Before creating a board profile, confirm the host can at least see the FPGA over JTAG:

```bash
lsusb
openFPGALoader --scan-usb
openFPGALoader --detect
```

Interpretation:
- If `openFPGALoader --detect` reports a Xilinx family and part, the physical JTAG path is working.
- That is a good first milestone, but it is still below "board support" because no board-specific build or runtime proof exists yet.

Example bounded success report:
- [artix7_100t_jtag_detection_2026-04-30.md](/home/ormastes/dev/pub/simple/doc/09_report/2026/04/artix7_100t_jtag_detection_2026-04-30.md)

Known board facts captured in repo:
- [mlk_s02_100t.sdn](/home/ormastes/dev/pub/simple/config/resources/boards/mlk_s02_100t.sdn)

Current generated RTL entrypoint:
- [simple_generated_fpga_rtl.md](/home/ormastes/dev/pub/simple/doc/07_guide/hardware/simple_generated_fpga_rtl.md)

Current `MLK-S02-100T` constraint scaffold:
- [mlk_s02_100t.xdc](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/constraints/mlk_s02_100t.xdc)

Current `MLK-S02-100T` wrapper/build scaffolds:
- [mlk_s02_100t_wrapper_stub.vhd](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/rtl/mlk_s02_100t_wrapper_stub.vhd)
- [build_mlk_s02_100t.tcl](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/build_mlk_s02_100t.tcl)
- [program_mlk_s02_100t.tcl](/home/ormastes/dev/pub/simple/examples/09_embedded/fpga_riscv/program_mlk_s02_100t.tcl)

Vendor bundle search and acquisition notes:
- [mlk_s02_100t_vendor_resource_search_2026-05-01.md](/home/ormastes/dev/pub/simple/doc/09_report/2026/05/mlk_s02_100t_vendor_resource_search_2026-05-01.md)

## Commands That Prove Only Partial Readiness

These are useful, but they do not prove board support by themselves:

```bash
bin/simple test doc/06_spec/app/hardware/feature/riscv_fpga_linux_spec.spl
bin/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl -- /tmp/fpga_bundle
```

What they prove:
- orchestration contracts parse and validate
- generic bundle generation works

What they do not prove:
- board pinout correctness
- Vivado success for a real part
- JTAG or hardware manager connectivity
- boot or runtime behavior on a physical FPGA

## Artix-7 100T Checklist

If the target is `MLK-S02-100T` or another Artix-7 100T board, complete this checklist before calling it supported:

- exact board model recorded in docs
- Xilinx part recorded in code and build scripts
- board-specific XDC committed
- top-level wrapper reviewed against board I/O and clocking
- Vivado synth/route/bitstream logs archived
- programming flow tested on real hardware
- authoritative spec or smoke test added for the hardware proof path
- lane status updated if the board graduates from historical or excluded status

## What Not To Do

- Do not reuse `constraints/zedboard.xdc` for an Artix-7 board.
- Do not keep `xilinx_generic` or `BOARD_PART_TBD` and call the board configured.
- Do not treat a generated manifest or passing unit spec as hardware validation.
