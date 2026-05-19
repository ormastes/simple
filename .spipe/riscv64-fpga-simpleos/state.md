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
- [ ] 2-research (Analyst)
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
<pending>

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
