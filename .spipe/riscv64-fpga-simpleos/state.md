# SStack State: riscv64-fpga-simpleos

## User Request
> Complete riscv64_fpga_simpleos_launch.md — implement the full RISC-V64 FPGA SimpleOS launch plan from hardware inventory through SimpleOS kernel FPGA platform, boot payload, and test harness. Use Sonnet agent teams with Opus advisor.

## Task Type
feature

## Refined Goal
> Implement the RISC-V64 FPGA SimpleOS launch infrastructure: hardware inventory/preflight scripts, SimpleOS RV64 FPGA platform kernel capsules (manifest-driven UART/timer/memory), bare-metal hello payload, riscv64-fpga-min boot profile, and skip-safe test harness — proving the path from host JTAG/UART detection to SimpleOS boot markers on the connected Xilinx FT4232H carrier board.

## Acceptance Criteria
- [ ] AC-1: `scripts/check-riscv64-fpga-simpleos-preflight.shs` exists and reports board USB IDs, serial ports, JTAG claim status, available synthesis/programming tools, RISC-V cross compiler versions, and pass/fail/blocked summary
- [ ] AC-2: Hardware inventory log generated under `doc/08_tracking/hardware/` with board model, FT4232H channel map, and udev permissions
- [ ] AC-3: JTAG-mode unbind/rebind script exists that temporarily releases the FTDI JTAG interface from ftdi_sio for programming, then rebinds
- [ ] AC-4: SimpleOS RV64 FPGA platform capsules exist: `src/os/kernel/arch/riscv64/platform/fpga.spl`, `manifest.spl`, `uart_mmio.spl`, `timer_mmio.spl`
- [ ] AC-5: `riscv64-fpga-min` boot profile defined — UART only, polling timer, no filesystem, no network, no framebuffer, initramfs or compiled smoke app
- [ ] AC-6: Hardware manifest format (`hardware_manifest.sdn`) defined with reset_pc, ram_base, ram_size, uart_base, timer_base, plic_base, hart_count, timebase_hz
- [ ] AC-7: Bare-metal RV64 FPGA hello payload builds with fixed linker address and UART MMIO write, producing expected proof string `SIMPLE-RV64-FPGA-HELLO board=<id> hart=0 pc=<addr>`
- [ ] AC-8: Test harness emits `BLOCKED` with reason (not false PASS) when hardware or tools are unavailable
- [ ] AC-9: No regression in existing QEMU RV64 SimpleOS smoke or RV32 GHDL lane

## Cooperative Providers
- Codex: unavailable (using Sonnet agents instead)
- Gemini: unavailable (Claude solo for design)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [x] 2-research (Analyst) — 2026-05-19
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** Implement RISC-V64 FPGA SimpleOS launch infrastructure
**ACs:** 9 acceptance criteria defined (AC-1 through AC-9)

**Existing assets identified:**
- FT4232H USB device (0403:6011) detected, serial ports /dev/ttyUSB{0,2,3,4,5}
- Toolchain available: openFPGALoader, openocd, riscv64-unknown-elf-gcc, riscv64-linux-gnu-gcc, ghdl
- Missing: vivado, yosys, nextpnr (synthesis tools)
- Track A (RTL): A1-A4 done (RV32I core, SoC, GHDL sim), A5-A8 not started
- Track B (QEMU boot): B1-B3 done (boot entry, TCP shim, IoDriver), B4-B6 blocked
- Existing scripts: check-kria-k26-fpga-bringup.shs, kria_jtag_axi_inventory.shs, kria_uart_check_sample.shs, rtl_riscv64_linux_generated.shs
- SimpleOS RV64 kernel files exist under src/os/kernel/ with freestanding boot chain (noalloc PMM, heap, log, services)
- doc/08_tracking/hardware/ directory does not exist yet

**Agent plan (mapped to launch plan agents):**
- Agent A: Hardware Inventory → Phase 5 sub-agent
- Agent B: RV64 Reference Softcore → Phase 2-3 research/design
- Agent C: SimpleOS RV64 FPGA Platform → Phase 5 sub-agent
- Agent D: Boot Loader and Payload → Phase 5 sub-agent
- Agent E: Test and CI Harness → Phase 4-5 sub-agent
- Agent F: SimpleOS Runtime Closure → Phase 5 sub-agent

### 2-research
**Date:** 2026-05-19
**Output:** `.spipe/riscv64-fpga-simpleos/research.md`

**FT4232H channel map (confirmed via sysfs):**
- Interface 0 = JTAG/MPSSE (Channel A) — NOT a ttyUSB under ftdi_sio; unbind `3-2:1.0` for openocd/openFPGALoader
- Interface 1 = ttyUSB2 (Channel B) — PS UART0 console at 115200
- Interface 2 = ttyUSB3 (Channel C) — PS UART1 or PL UART
- Interface 3 = ttyUSB5 (Channel D) — spare/platform UART
- ttyUSB0/ttyUSB4 are on a different hub node, not the ML Carrier Card FT4232H

**SDN format:** `table_name |col1, col2, ...|` header + 4-space-indented comma-rows; strings in `""`, integers and booleans bare.

**SHS pattern:** `pass()/fail()/info()` helpers, env-var config block at top, `/tmp/script.$$` temp files, script exits 0 always (caller parses output).

**Existing RV64 arch:** 19 files in `src/os/kernel/arch/riscv64/`, no `platform/` subdir yet. Linker loads at `0x80200000` (QEMU virt). FPGA needs new `platform/fpga_linker.ld` with board-specific memory map.

**Target contract:** `riscv_linux_target_contract()` exists in `riscv_target.spl`; no baremetal/fpga preset for rv64. Need `preset_riscv64_fpga` or `preset_riscv64_baremetal` analogous to `preset_riscv32_baremetal`.

**Linker scripts:** `src/os/kernel/arch/riscv64/linker.ld` is QEMU-only (0x80200000). Baremetal templates at `src/compiler/70.backend/baremetal/riscv/linker.ld` and `src/lib/nogc_async_mut_noalloc/baremetal/riscv/linker.ld`.

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
