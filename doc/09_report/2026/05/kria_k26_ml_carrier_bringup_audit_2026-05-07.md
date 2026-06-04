# Kria K26 ML Carrier Bring-Up Audit - 2026-05-07

## Objective

Check the newly connected FPGA board, research how to use it, inspect UART first, bootstrap hello world, then load a Simple-made RV64 image, boot SimpleOS, and open a database-backed web server.

## Hardware Identity

- USB identity: `Xilinx_ML_Carrier_Card_XFL1OSWWFM2B`
- USB product: `ML Carrier Card`
- Vivado hardware target: `localhost:3121/xilinx_tcf/Xilinx/XFL1OSWWFM2BA`
- Vivado devices: `xck26_0 arm_dap_1`
- Vivado device properties: `PART=xck26` for `xck26_0`, `PART=arm_dap` for `arm_dap_1`, empty `PROGRAM.FILE`

## UART And JTAG Evidence

- FTDI interface 0 was not bound to a tty driver.
- FTDI interfaces 1, 2, and 3 were bound by `ftdi_sio` as `ttyUSB1`, `ttyUSB2`, and `ttyUSB3`.
- UART sampling at 115200 8N1 returned no bytes on `ttyUSB1`, `ttyUSB2`, or `ttyUSB3`.
- `openFPGALoader -c ft4232 --detect` opened the adapter but reported an empty JTAG chain.
- XSDB launched `hw_server` but did not list usable `targets` or `jtag targets`.

## Network Evidence

- mDNS names `kria.local`, `xilinx.local`, `petalinux.local`, and `ubuntu.local` did not resolve.
- ARP discovery found `192.168.1.126` with only SSH open and banner `SSH-2.0-OpenSSH_10.2`.
- Public-key SSH attempts to `192.168.1.126` for `ubuntu`, `petalinux`, `xilinx`, `root`, and `ormastes` were rejected.
- `192.168.1.126` remains only a candidate embedded target until credentials or board identity are confirmed.

## Research References

- AMD K26 SOM data sheet: `https://docs.amd.com/r/en-US/ds987-k26-som/Ordering-Information`
- AMD Kria boot firmware overview: `https://xilinx.github.io/kria-apps-docs/bootfw/build/html/docs/bootfw_overview.html`
- AMD Kria FTDI/JTAG/UART guide: `https://xilinx.github.io/kria-apps-docs/creating_applications/2022.1/build/html/docs/FTDI_EEPROM_design_guide.html`

## Local Validation Completed

- `bin/simple run examples/01_getting_started/hello_native.spl` printed `Hello World`.
- Built `examples/09_embedded/baremetal/baremetal/hello_riscv64.s` with `riscv64-linux-gnu-as` / `riscv64-linux-gnu-ld`; `qemu-system-riscv64 -machine virt -bios none -kernel build/rv64_bringup_check/hello_riscv64.elf` printed `Hello, RISC-V 64!`.
- `bin/simple test test/03_system/qemu/rv64gc_qemu_boot_spec.spl --mode=interpreter` passed 14 examples.
- RISC-V semihost hello passed in GHDL with `Hello, RISC-V 32!` and `[SEMIHOST TEST] Success - exit code 0`.
- `bin/simple test test/01_unit/os/qemu_runner_spec.spl --mode=interpreter` passed 55 examples, including RV64 hosted and RV64 VirtIO FAT32 SMF scenario checks.
- `bin/simple test test/03_system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl --mode=interpreter` passed 3 examples, proving the RV64 hosted QEMU command includes disk and SSH/HTTP host-forwarding.
- Rebuilt `src/compiler_rust/target/debug/simple` with `LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 cargo build --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --features llvm --bin simple`.
- Created `build/os/fat32-riscv64.img` with `sh scripts/os/make_os_disk.shs 64 build/os/fat32-riscv64.img "" riscv64`.
- `timeout 180 bin/simple run examples/simple_os/run.spl -- --arch=riscv64` built `build/os/simpleos_riscv64_smf_fs.elf`, booted under `qemu-system-riscv64`, and printed `SIMPLEOS_RISCV_SMF_FS_PASS` plus `TEST PASSED`.
- `bin/simple test test/02_integration/app/web_stack_sample_persistence_spec.spl --mode=interpreter` passed 1 example.
- `bin/simple test test/02_integration/app/web_stack_sample_spec.spl --mode=interpreter` passed 4 examples.
- Host-side SQLite HTTP wrapper is running at `http://127.0.0.1:3080` from `build/web_stack_sample/live_server.py` with DB `build/web_stack_sample/live.sqlite3`; `GET /api/items` returned rows for `Kria K26 bring-up` and `Web stack sample`.

## Artifact And Toolchain Findings

- No ready Kria/XCK26 `.bit` or `.xsa` artifact was found in the repo areas checked.
- The only FPGA `.bit` files found were MLK-S02/Artix-7 demo outputs under `examples/09_embedded/fpga_riscv/build_mlk_s02_100t_*`; they are not compatible with the detected K26 target.
- A build-only K26 PL smoke attempt failed before synthesis because this Vivado install does not expose `xck26-sfvc784-2LV-c`, `xck26-sfvc784-2LVI-i`, or matching K26 board parts through `get_parts` / `get_board_parts`.
- Installed K26 board XMLs reference `xck26-sfvc784-2LV-c` and `xck26-sfvc784-2LVI-i`, but Vivado reports those parts invalid or unavailable.
- The initial RV64 SimpleOS run failed because the selected Rust compiler lacked the `llvm` feature; rebuilding with LLVM 18 resolved this local QEMU blocker.
- `examples/web_stack_sample/main.spl` is a persistence/preflight entrypoint, not a socket listener; the live HTTP proof uses the generated host wrapper in `build/web_stack_sample/live_server.py`.

## Completion Audit

| Requirement | Status | Evidence |
| --- | --- | --- |
| Check new FPGA connection | Partial | Vivado sees `xck26_0 arm_dap_1`; openFPGALoader chain is empty |
| Research web usage | Done | AMD references listed above |
| Make guide/report doc | Done | This report |
| First check UART log | Done, negative | No bytes on `ttyUSB1..3` |
| Bootstrap hello world | Done | `Hello World` from `hello_native.spl` |
| Bootstrap RV64 locally | Done | RV64 ELF printed `Hello, RISC-V 64!` in QEMU; RV64GC QEMU spec passed |
| Load Simple-made RV64 on FPGA | Not done | No K26 bitstream/XSA and no usable target load path |
| Load/start SimpleOS locally | Done | RV64 SimpleOS QEMU boot printed `SIMPLEOS_RISCV_SMF_FS_PASS` and `TEST PASSED` |
| Load/start SimpleOS on FPGA | Not done | No board boot or image deployment evidence |
| Open web server with DB locally | Done | `http://127.0.0.1:3080` serves rows from `build/web_stack_sample/live.sqlite3` |
| Open web server with DB on target | Not done | No target deployment or HTTP proof |

## Current Physical-Board Blockers

- No UART boot log was captured from the physical board.
- No deployable K26/Kria bitstream or XSA is available.
- The local Vivado install lacks K26 synthesis parts, so it cannot build even a minimal K26 PL smoke bitstream.
- XSDB does not expose usable processor/debug targets for a bare-metal load.
- Candidate SSH host `192.168.1.126` cannot be used without valid credentials or confirmed board identity.
- Physical target web deployment remains blocked until board identity, login, or a usable JTAG/boot path is available.
