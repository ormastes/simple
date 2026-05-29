# RISC-V64 FPGA SimpleOS Launch Plan
<!-- codex-design -->

**Date:** 2026-05-19
**Status:** active hardware bring-up plan

## Goal

Launch a 64-bit RISC-V softcore on the connected FPGA board and boot SimpleOS
far enough to prove:

- FPGA programming and UART/JTAG are controlled from this host;
- a known RV64 payload runs from FPGA memory and emits a serial proof;
- the SimpleOS RISC-V kernel enters its boot path on the FPGA target;
- interrupts, timer, memory map, and console are stable enough for a minimal
  SimpleOS shell or smoke app;
- every failure is captured as a concrete bug or hardware gap, not a loose TODO.

## Local Hardware Facts

Observed on this host:

- USB FTDI/Xilinx device: `0403:6011`, model `ML_Carrier_Card`, serial
  `XFL1OSWWFM2B`.
- Serial ports:
  - `/dev/ttyUSB2`, interface `01`
  - `/dev/ttyUSB3`, interface `02`
  - `/dev/ttyUSB5`, interface `03`
- `openFPGALoader -c ft4232 --detect` currently fails because `ftdi_sio` has
  claimed the FT4232H interfaces.
- Installed tools:
  - `openocd`
  - `openFPGALoader`
  - `riscv64-unknown-elf-gcc`
  - `riscv64-linux-gnu-gcc/as/ld`
  - `ghdl`
- Missing tools:
  - `vivado`
  - `yosys`
  - `nextpnr-*`
  - `litex_*`
  - `quartus`

## Existing Repo State

- `doc/plans/riscv_rtl_simpleos_boot.md` is the main RISC-V RTL + SimpleOS boot
  plan.
- `examples/09_embedded/fpga_riscv/README.md` states the current in-repo
  runnable FPGA CPU lane is handwritten RV32I, GHDL-validated, and not a
  generated RV64 SimpleOS-capable core.
- `scripts/check-kria-k26-fpga-bringup.shs` already probes UART, Xilinx/JTAG
  detection, Simple hello, and GHDL RISC-V hello.
- `scripts/rtl_riscv64_linux_generated.shs` and
  `scripts/check-riscv-rtl-linux-smoke.shs` are existing generated RV64 Linux
  proof lanes.
- `scripts/make_os_disk.shs` has RISC-V image lanes, including `riscv64`.

## Board Strategy

Treat the connected Xilinx carrier as two systems:

1. **Management system:** the board's native Xilinx/Zynq/Kria path that loads PL
   bitstreams, exposes UART/JTAG, and may run Linux on the ARM PS.
2. **Target system:** an RV64 softcore synthesized into PL, with its own memory
   map, UART, timer, interrupt controller, and boot ROM.

Do not try to replace the board's native PS boot firmware in the first phase.
Use PS/JTAG only to load and observe the RISC-V softcore.

## Target Architecture

```text
Host
  -> openFPGALoader/Vivado Lab/JTAG
  -> Xilinx carrier PL bitstream
  -> RV64 softcore
       -> boot ROM
       -> SRAM/BRAM smoke payload
       -> DDR-backed SimpleOS payload
       -> UART console
       -> CLINT/PLIC-compatible timer/interrupt model
       -> optional block-device bridge
```

## Phase 0: Non-Destructive Hardware Inventory

### Tasks

- Confirm exact board model from USB, silkscreen, vendor files, or Vivado board
  part.
- Map FT4232H channels:
  - JTAG/MPSSE channel
  - UART console channel
  - auxiliary UARTs
- Record required udev permissions for `dialout`, `plugdev`, and USB access.
- Sample all three Xilinx serial ports at common baud rates:
  - 115200
  - 921600
  - 1500000
- Add an inventory log under `doc/08_tracking/hardware/`.

### Problems

- `ftdi_sio` currently claims all FT4232H serial interfaces, so
  openFPGALoader cannot claim the JTAG channel.
- Vivado is missing, so vendor Hardware Manager cannot be used locally.
- Exact board constraints are not yet proven.

### Solutions

- Add a documented "JTAG mode" script that temporarily unbinds only the FTDI
  interface needed for JTAG, then rebinds it after programming.
- Keep UART interfaces bound to `ftdi_sio` when only serial logging is needed.
- If the FTDI EEPROM is not configured for Xilinx JTAG, document the Vivado
  `program_ftdi` route, but do not rewrite EEPROM automatically.
- Support a remote Vivado machine as a fallback programming backend.

## Phase 1: Toolchain Gate

### Tasks

- Keep the host-native smoke lane:

```bash
scripts/check-kria-k26-fpga-bringup.shs --local-only
```

- Add a new hardware preflight script:

```bash
scripts/check-riscv64-fpga-simpleos-preflight.shs
```

It should report:

- board USB IDs;
- serial ports;
- JTAG claim status;
- available synthesis/programming tools;
- RISC-V cross compiler versions;
- existing SimpleOS RV64 build artifacts;
- pass/fail/blocked summary.

### Problems

- Open-source Xilinx 7-series/UltraScale synthesis support may not be enough for
  the connected board.
- Vivado license/tool installation may be required for real bitstream builds.

### Solutions

- Split the toolchain into three backends:
  - `vivado-local`
  - `vivado-remote`
  - `prebuilt-bitstream`
- Do not block software bring-up on local synthesis if a known-good bitstream is
  available.

## Phase 2: RV64 Softcore Selection

### Options

| Option | Description | Pros | Cons | Use |
|--------|-------------|------|------|-----|
| A | Generate minimal repo-native RV64 core | Maximum control; aligns with Simple hardware work | Highest risk; needs MMU/timer/interrupt work | Long-term |
| B | Use LiteX/VexRiscv-SMP or Rocket RV64 as reference lane | Proven FPGA Linux-style path; easier OpenSBI/device-tree story | Adds external generator/tool dependency | Bring-up |
| C | Extend existing RV32I handwritten core to RV64 | Reuses current GHDL lane | Too large a jump for SimpleOS; no supervisor platform | Avoid for first RV64 SimpleOS |

### Decision

Use **Option B** for first hardware SimpleOS proof, while keeping Option A as the
repo-native target. The first milestone should not depend on inventing a new
RV64 core and debugging SimpleOS simultaneously.

## Phase 3: Minimal FPGA Payload Before SimpleOS

### Tasks

- Build RV64 bare-metal hello with:
  - fixed linker address;
  - UART MMIO write;
  - trap vector;
  - timer read if available.
- Load through boot ROM, JTAG memory write, or UART loader.
- Expected UART proof:

```text
SIMPLE-RV64-FPGA-HELLO board=<id> hart=0 pc=<addr>
```

### Problems

- Unknown UART base address and clock divisor.
- Unknown reset PC and memory address.
- Unknown endian/width behavior on softcore bus.

### Solutions

- Generate `hardware_manifest.sdn` from the SoC build with:
  - `reset_pc`
  - `ram_base`
  - `ram_size`
  - `uart_base`
  - `timer_base`
  - `plic_base`
  - `hart_count`
- Make SimpleOS consume the same manifest for linker script and device table.

## Phase 4: SimpleOS RV64 Kernel Handoff

### Tasks

- Build `build/simpleos-rv64-fpga.elf` with:
  - `--target riscv64-fpga`
  - no host syscalls;
  - no virtio assumptions;
  - UART console selected from manifest;
  - physical memory from manifest;
  - timer interrupt from CLINT-like block or polling fallback.
- Add FPGA-specific platform capsule:
  - `src/os/kernel/arch/riscv64/platform/fpga.spl`
  - `src/os/kernel/arch/riscv64/platform/manifest.spl`
  - `src/os/kernel/arch/riscv64/platform/uart_mmio.spl`
  - `src/os/kernel/arch/riscv64/platform/timer_mmio.spl`
- Keep QEMU `virt` platform separate.

### Problems

- QEMU `virt` device assumptions can leak into FPGA code.
- SimpleOS may expect block storage, networking, framebuffer, or virtio too
  early.
- M-mode/S-mode split may not exist on the chosen softcore.

### Solutions

- Add a `riscv64-fpga-min` boot profile:
  - UART only;
  - polling timer allowed;
  - no filesystem mount required;
  - no network;
  - no framebuffer;
  - initramfs or compiled smoke app.
- If S-mode is unavailable, start with an M-mode SimpleOS boot profile and
  document the missing supervisor boundary as a blocker.
- If S-mode is available, boot through OpenSBI and pass a device tree.

## Phase 5: SimpleOS Storage and Apps

### Tasks

- Stage 1: compiled-in initramfs with `/init`.
- Stage 2: memory-backed block device loaded with the bitstream or UART loader.
- Stage 3: SD/eMMC bridge if the board design exposes one to the softcore.
- Reuse `scripts/make_os_disk.shs` only after block-device geometry is real.

### Problems

- The native Kria PS has eMMC/SD; the RV64 softcore in PL does not automatically
  own those devices.
- A block-device bridge can introduce coherency and security hazards.

### Solutions

- Do not claim SimpleOS disk boot until the softcore has a real block path.
- Use initramfs for first shell proof.
- File a separate bridge design for PS-to-PL storage if needed.

## Phase 6: Interrupts, Timer, and SMP

### Tasks

- Implement single-hart first.
- Add timer tick proof:

```text
SIMPLE-RV64-FPGA-TICK count=10
```

- Add external interrupt proof only after UART and timer are stable.
- Add secondary harts only after the boot CPU can run SimpleOS shell.

### Problems

- OpenSBI expects a coherent hart/timer/interrupt model.
- FPGA timer frequency may differ from the manifest.

### Solutions

- Require manifest-provided `timebase_hz`.
- Add boot-time calibration diagnostics.
- Gate SMP behind a separate `riscv64-fpga-smp` profile.

## Phase 7: Debug and Observability

### Required Logs

- host preflight log;
- JTAG detect log;
- bitstream build/program log;
- UART boot transcript;
- SimpleOS boot markers;
- panic/trap dump.

### Required Boot Markers

```text
SIMPLE-RV64-FPGA-BOOT entry
SIMPLE-RV64-FPGA-MEM ok
SIMPLE-RV64-FPGA-UART ok
SIMPLE-RV64-FPGA-TIMER ok
SIMPLE-RV64-FPGA-SCHED ok
SIMPLE-RV64-FPGA-SHELL ok
```

## Agent Breakdown

### Agent A: Hardware Inventory

- Owns USB/JTAG/UART detection.
- Produces `doc/08_tracking/hardware/riscv64_fpga_inventory_<date>.md`.
- Adds `scripts/check-riscv64-fpga-simpleos-preflight.shs`.

### Agent B: RV64 Reference Softcore Lane

- Owns external/reference RV64 SoC generation.
- Produces bitstream manifest and hardware manifest.
- Must keep generated artifacts out of source unless small and intentional.

### Agent C: SimpleOS RV64 FPGA Platform

- Owns kernel platform separation from QEMU `virt`.
- Adds `riscv64-fpga-min` profile.
- Adds manifest-driven UART/timer/memory selection.

### Agent D: Boot Loader and Payload Handoff

- Owns boot ROM, JTAG/UART load, linker script, and payload packaging.
- Must prove bare-metal hello before SimpleOS.

### Agent E: Test and CI Harness

- Owns GHDL/QEMU/hardware smoke tests.
- Adds skip-safe hardware tests that report `BLOCKED` when hardware/tools are
  unavailable, not false PASS.

### Agent F: SimpleOS Runtime Closure

- Owns initramfs, shell smoke, panic path, timer tick, and follow-on storage.

## Acceptance Gates

### Gate 1: Inventory

```bash
scripts/check-riscv64-fpga-simpleos-preflight.shs
```

Pass requires board, UART, toolchain, and JTAG status classified.

### Gate 2: Simulation

```bash
scripts/check-riscv-rtl-linux-smoke.shs
scripts/rtl_riscv64_linux_generated.shs
```

Pass requires RV64 generated/reference lane still works before hardware changes.

### Gate 3: FPGA Hello

Pass requires UART transcript with `SIMPLE-RV64-FPGA-HELLO`.

### Gate 4: SimpleOS Boot Markers

Pass requires UART transcript through:

```text
SIMPLE-RV64-FPGA-SHELL ok
```

### Gate 5: Regression

Pass requires no regression in QEMU RV64 SimpleOS smoke and no regression in the
existing RV32 GHDL lane.

## Problem Register

| ID | Problem | Impact | Solution |
|----|---------|--------|----------|
| RV64-FPGA-001 | JTAG blocked by `ftdi_sio` claim | Cannot program/detect through openFPGALoader | Add unbind/rebind script and document Vivado fallback |
| RV64-FPGA-002 | Vivado missing on host | Cannot synthesize/program Xilinx bitstreams locally | Support remote Vivado and prebuilt-bitstream lanes |
| RV64-FPGA-003 | Current repo FPGA CPU is RV32I | Cannot run RV64 SimpleOS directly | Use reference RV64 softcore first; keep repo-native RV64 as long-term |
| RV64-FPGA-004 | Board constraints not authoritative | Bitstream may fail timing or pinout | Require vendor XDC/board files before hardware PASS |
| RV64-FPGA-005 | QEMU `virt` assumptions in RISC-V kernel | FPGA boot can hang on missing virtio/PLIC layout | Add manifest-driven `riscv64-fpga-min` platform |
| RV64-FPGA-006 | No proven PL DDR path | SimpleOS cannot load real kernel/apps | Start in BRAM/SRAM hello, then add DDR controller proof |
| RV64-FPGA-007 | No storage path to softcore | Filesystem boot cannot work | Use initramfs first; design PS-to-PL or SD bridge later |
| RV64-FPGA-008 | Unknown privilege model | OpenSBI/S-mode may be unavailable | Support M-mode minimal profile first; add OpenSBI only if hardware supports it |
| RV64-FPGA-009 | Timer/interrupt model unknown | Scheduler cannot run reliably | Require CLINT/PLIC-compatible blocks or polling fallback |
| RV64-FPGA-010 | Hardware tests can false-pass when tools missing | Misleading status | Tests must emit BLOCKED with reason when hardware/tool missing |

## External Research Notes

- AMD UG908 documents that FTDI devices such as FT4232H need Xilinx-compatible
  EEPROM configuration to appear as Xilinx JTAG cables in Vivado/XSDB.
- AMD Kria documentation describes K26/Kria workflows as PS + PL systems where
  Vivado/Vitis/PetaLinux or Ubuntu firmware flows load PL bitstreams and
  associated device-tree overlays.
- RISC-V Linux-style boot flows normally use an SBI layer such as OpenSBI before
  S-mode software; SimpleOS should not assume S-mode exists on a minimal FPGA
  softcore until the selected core proves it.

## Next Concrete Step

Implement Agent A first:

```bash
scripts/check-riscv64-fpga-simpleos-preflight.shs
```

Do not start SimpleOS kernel changes until the preflight report names the exact
board, UART channel, JTAG strategy, and available bitstream build/programming
backend.
