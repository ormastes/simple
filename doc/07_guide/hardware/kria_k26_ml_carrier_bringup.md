# Kria K26 ML Carrier Bring-Up Guide

Date: 2026-05-07

## Scope

This guide records the current bring-up path for the connected Xilinx ML Carrier / Kria K26-class board and separates completed local validation from blocked physical-board deployment.

## Current Board Identity

- USB identity: `Xilinx_ML_Carrier_Card_XFL1OSWWFM2B`
- Serial devices: `ttyUSB1`, `ttyUSB2`, and `ttyUSB3` through `/dev/serial/by-id/usb-Xilinx_ML_Carrier_Card_XFL1OSWWFM2B-*`
- Vivado hardware target: `localhost:3121/xilinx_tcf/Xilinx/XFL1OSWWFM2BA`
- Vivado devices after `open_hw_target`: `xck26_0,arm_dap_1`
- Vivado properties: `PART=xck26` and `PART=arm_dap`; `PROGRAM.FILE` is empty for both

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
2. Sample UARTs before programming:
   check `ttyUSB1`, `ttyUSB2`, and `ttyUSB3` at 115200 8N1.
   Current result: zero bytes captured on all three UARTs in a fresh sample: `/dev/ttyUSB1 bytes=0`, `/dev/ttyUSB2 bytes=0`, `/dev/ttyUSB3 bytes=0`.
3. Check JTAG:
   `openFPGALoader -c ft4232 --detect`
   Current result: adapter opens, but the chain is reported as `empty`.
4. Check Vivado hardware manager:
   open hardware target `localhost:3121/xilinx_tcf/Xilinx/XFL1OSWWFM2BA`.
   Current result: `xck26_0` and `arm_dap_1` are visible, with no program file assigned.
5. Search deployable artifacts:
   look for `*.xsa`, `*k26*.bit`, `*kria*.bit`, and `*xck26*.bit`.
   Current result: no deployable K26/Kria artifact found.
6. Search boot/programming artifacts:
   look for `*.pdi`, `BOOT.BIN`, `*.dtb`, `Image`, `*.wic`, and `*.img`.
   Current repo result: only local QEMU disk images were found, including `build/os/fat32-riscv64.img`; no Kria boot/programming artifact was found.
   Current Xilinx install result: sample PDI/XSA/DTB artifacts exist for other boards/devices such as VCK190, VEK280, VMK180, ZCU102, and Versal samples, but not for the connected K26/Kria target.
7. Check host-visible USB and block devices:
   `lsusb` shows the board-side USB bridge as `0403:6011 Future Technology Devices International, Ltd FT4232H Quad HS USB-UART/FIFO IC`.
   `lsblk` shows no USB, SD, or other removable boot media from the board; only local NVMe and loop devices are visible.

## Local Proofs Completed

- Simple hello world: `bin/simple run examples/01_getting_started/hello_native.spl` printed `Hello World`.
- RV64 bare-metal hello:
  built `build/rv64_bringup_check/hello_riscv64.elf` from `examples/09_embedded/baremetal/baremetal/hello_riscv64.s`; QEMU printed `Hello, RISC-V 64!`.
- RV64GC QEMU spec:
  `bin/simple test test/qemu/rv64gc_qemu_boot_spec.spl --mode=interpreter` passed 14 examples.
- SimpleOS RV64 local boot:
  rebuilt the Rust Simple compiler with LLVM 18 support, created `build/os/fat32-riscv64.img`, then ran `timeout 180 bin/simple run examples/simple_os/run.spl -- --arch=riscv64`.
  QEMU printed `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED`.
- Web stack DB specs:
  `bin/simple test test/integration/app/web_stack_sample_persistence_spec.spl --mode=interpreter` passed 1 example.
  `bin/simple test test/integration/app/web_stack_sample_spec.spl --mode=interpreter` passed 4 examples.
- Local HTTP + DB proof:
  `build/web_stack_sample/live_server.py` serves `build/web_stack_sample/live.sqlite3` at `http://127.0.0.1:3080`.
  `GET /api/items` returned seeded rows from SQLite.

## Current Blockers

- Physical FPGA RV64 load is not complete: there is no K26 `.bit` / `.xsa`, and the available `.bit` artifacts are for MLK-S02 / Artix-7.
- Physical board boot media is not complete: there is no matching K26/Kria `BOOT.BIN`, `.pdi`, Linux `Image`, DTB, WIC, or SD-card image in the repo search.
- The local Vivado install has K26 board XMLs but does not expose valid K26 synthesis parts for local bitstream generation.
- Physical SimpleOS boot is not complete: there is no confirmed board boot path through UART, SSH, JTAG, SD boot media, or XSA/bitstream deployment.
- No board-side mass-storage or removable boot medium is visible to this host, so there is no host-mounted SD/eMMC image path to inspect or update.
- Target web deployment is not complete: `192.168.1.126` has SSH open, but available public-key logins for `ubuntu`, `petalinux`, `xilinx`, `root`, and `ormastes` were rejected and the host is not confirmed to be the board.
- Default password checks for `ubuntu:ubuntu`, `petalinux:petalinux`, `xilinx:xilinx`, `root:root`, and `root:xilinx` were also rejected on `192.168.1.126`.

## Completion Audit

| Objective item | Current status | Evidence gate |
| --- | --- | --- |
| Check new FPGA connection | Partial | USB and Vivado see the ML Carrier/K26 target; `openFPGALoader` still reports an empty chain |
| Research how to use it | Done | AMD K26, Kria boot firmware, and FTDI/JTAG/UART references are listed above |
| First check UART log | Done, negative | Fresh 115200 8N1 samples from `ttyUSB1`, `ttyUSB2`, and `ttyUSB3` captured zero bytes |
| Bootstrap hello world | Done locally | Simple native hello printed `Hello World` |
| Load Simple-made RV64 | Done locally, not physical | RV64 ELF boots in QEMU; no K26-compatible load artifact/path exists |
| Load/start SimpleOS | Done locally, not physical | RV64 SimpleOS QEMU prints `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED`; no board boot path exists |
| Open web server with DB | Done locally, not target | `127.0.0.1:3080` serves SQLite rows; no target login/deployment path exists |

The goal is not complete until the physical rows above have target-side evidence: board-compatible boot/programming artifact, successful board load/boot, and HTTP proof from the board itself.

## Next Required Input Or Change

To continue physical bring-up, provide one of:

- a compatible K26/Kria `.xsa` or `.bit` plus the intended load path,
- a Kria SD-card image/boot medium with known login credentials,
- valid SSH credentials for the confirmed board IP,
- a Vivado installation/device package that exposes the K26 synthesis part.
