# SStack State: unoq-simpleos-port

## User Request
> port simple os to uno q board research about the board which linked current host and load on the board fix if there is bug and update or make dev board guide

## Task Type
feature

## Refined Goal
> Port SimpleOS baremetal support to the Arduino UNO Q board's MCU subsystem (STM32U585 / ARM Cortex-M33 @ 160 MHz, 2 MB flash, 786 KB SRAM). Create target definition, compiler preset, remote execution adapter, and update the embedded board guide. Verify connectivity to the physically connected board (USB ID 2341:0078, serial ttyACM0) and test basic code upload/execution.

## Board Reference
- **Board**: Arduino UNO Q (ABX00162), 2GB variant
- **MPU**: Qualcomm QRB2210 Dragonwing (Cortex-A53 quad @ 2.0 GHz, 2 GB LPDDR4, 16 GB eMMC, Debian Linux)
- **MCU**: STM32U585 (Cortex-M33 @ 160 MHz, 2 MB flash, 786 KB SRAM, FPU, Zephyr OS)
- **USB ID**: 2341:0078
- **Host serial**: /dev/ttyACM0 (serial: Arduino_Uno_Q_-_uno-q_3655308719)
- **Interfaces**: I2C/I3C, SPI, PWM, CAN, UART, PSSI, GPIO, JTAG, ADC
- **Debug**: JTAG via JCTL header, Arduino App Lab, Arduino IDE 2.0+

## Acceptance Criteria
- [ ] AC-1: Cortex-M33 target preset added to `src/compiler/70.backend/target_presets.spl` with correct memory map (flash 0x08000000, SRAM 0x20000000, 2 MB / 786 KB)
- [ ] AC-2: STM32U585 target definition created at `src/lib/nogc_sync_mut/debug/remote/target/stm32u5.spl` (wraps ArmCortexMTarget with M33-specific config)
- [ ] AC-3: UNO Q remote execution adapter created at `src/lib/nogc_sync_mut/debug/remote/exec/adapter_uno_q.spl` (connects via /dev/ttyACM0, implements ExecTarget)
- [ ] AC-4: Host detects and connects to the UNO Q board via serial (verify ttyACM0 communication)
- [ ] AC-5: Embedded board guide (`doc/07_guide/embedded_board_guide.md`) updated with UNO Q section (board-specific notes, memory map, quick start)
- [ ] AC-6: Hardware manifest (`doc/08_tracking/hardware/hardware_manifest.sdn`) updated with UNO Q entry
- [ ] AC-7: No regressions in existing STM32H7/WB/Arduino R4 adapters

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-20
- [x] 2-research (Analyst) — 2026-05-20
- [x] 3-arch (Architect) — 2026-05-20
- [x] 4-spec (QA Lead) — 2026-05-20
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type**: feature
**Refined goal**: Port SimpleOS baremetal to Arduino UNO Q MCU (STM32U585 / Cortex-M33). Add target preset, target def, adapter, board guide, and verify serial connectivity.

**Key findings from research**:
- UNO Q is a dual-chip board: QRB2210 MPU (Linux) + STM32U585 MCU (Zephyr/Arduino)
- MCU is the baremetal target — Cortex-M33, 2 MB flash, 786 KB SRAM
- Existing STM32H7 (M7) and STM32WB (M4) adapters provide a template
- Board connected at /dev/ttyACM0 (USB 2341:0078)
- No Cortex-M33 preset exists yet — need new `preset_cortex_m33()` in target_presets.spl

**7 ACs defined** covering compiler preset, target def, adapter, connectivity, docs, manifest, and regression check.

### 2-research

## Research Summary

### Critical Finding: Debug Connectivity Gap

The UNO Q's USB interface exposes **Vendor-Specific + CDC ACM** (serial) — it does **NOT** have a CMSIS-DAP debug interface like the Arduino R4 WiFi. This means the existing OpenOCD-over-CMSIS-DAP adapter pattern (used by `ArduinoR4Adapter`) is not directly available. The STM32H7 adapter pattern (ST-Link via OpenOCD) also requires an external probe.

**Actual device**: `/dev/ttyACM2` (not ttyACM0 as initially assumed — the R4 WiFi occupies ttyACM0/1). Serial: `3655308719`. Symlink: `/dev/serial/by-id/usb-Arduino_Uno_Q_-_uno-q_3655308719-if01`.

**Options for architect (phase 3) to choose**:
1. **External JTAG/SWD probe on JCTL header** — OpenOCD has `stm32u5x.cfg` (verified present in 0.12.0), existing adapter pattern fits directly. Requires separate hardware (ST-Link V2/V3, J-Link, or CMSIS-DAP probe).
2. **DFU bootloader** — STM32U585 has ROM DFU (enter via BOOT0+reset). Uses `dfu-util` for flash programming. No SRAM-exec pipeline, but sufficient for flash-and-run workflow.
3. **MPU-side bridge** — The Qualcomm QRB2210 MPU runs Linux and could broker debug access to the MCU. Speculative, requires investigation of Arduino's firmware bridge.
4. **CDC-ACM serial only** — Satisfies AC-4 (serial communication) but NOT AC-3 (SRAM upload/execute pipeline).

### Existing Code

- `src/lib/nogc_sync_mut/debug/remote/target/stm32h7.spl` — `Stm32H7Target` class wrapping `ArmCortexMTarget.cortex_m7()`. Template for `Stm32U5Target`. Fields: `core`, `stlink_serial`, `openocd_cfg`, `gdb_port`. Methods: `flash_base()` (0x08000000), `sram_base()` (0x24000000), `sram_size()` (1 MB).
- `src/lib/nogc_sync_mut/debug/remote/target/stm32wb.spl` — `Stm32WbTarget`, same pattern with `cortex_m4()`. SRAM base 0x20000000, 256 KB.
- `src/lib/nogc_sync_mut/debug/remote/target/arm_cortex_m.spl` — Base class `ArmCortexMTarget` with factory methods `cortex_m4()` and `cortex_m7()`. **No `cortex_m33()` exists yet** — must be added. Fields: `_registers`, `_hw_bp_count`, `_hw_wp_count`, `_core_name`. M7: 6 HW breakpoints; M4: 4 HW breakpoints; M33: typically 8 HW breakpoints.
- `src/lib/nogc_sync_mut/debug/remote/exec/adapter_stm32h7.spl` — `Stm32H7Adapter`, OpenOCD telnet-based. Uses `MemoryMap.stm32h7()`, ports 23333/24444/26666. Pattern: start OpenOCD, telnet `mww`/`mdw`/`reg` commands.
- `src/lib/nogc_sync_mut/debug/remote/exec/adapter_arduino_r4.spl` — `ArduinoR4Adapter`, OpenOCD via CMSIS-DAP/SWD. Uses `MemoryMap.arduino_r4()`, ports 25333/25444/25666. OpenOCD args: `cmsis-dap.cfg` + `renesas_s7g2.cfg`.
- `src/lib/nogc_sync_mut/debug/remote/exec/types.spl` — `MemoryMap` class with factory functions for all targets. **No `uno_q()` exists** — must be added.
- `src/compiler/70.backend/target_presets.spl` — `TargetPreset` struct + factory functions. Has `preset_cortex_m4()` (thumbv7em, eabihf) and `preset_cortex_m0()` (thumbv6m, eabi). **No `preset_cortex_m33()` exists** — must be added. `preset_by_name()` at line 239 needs new elif branch. `preset_all_names()` at line 283 needs new entry.
- `doc/07_guide/embedded_board_guide.md` — Section 7 has board-specific notes for STM32H7, STM32WB, Arduino R4, etc. Section 2 has memory map table. Both need UNO Q entries.
- `doc/08_tracking/hardware/hardware_manifest.sdn` — SDN table format: `id, field, value, unit, notes`. Currently has ML_Carrier_Card. Needs UNO Q entries.

### Reusable Modules

- `std.nogc_sync_mut.debug.remote.target.arm_cortex_m.ArmCortexMTarget` — base class, needs `cortex_m33()` factory added
- `std.nogc_sync_mut.debug.remote.exec.types.MemoryMap` — needs `uno_q()` factory added
- `std.nogc_sync_mut.debug.remote.exec.manager.RemoteExecutionManager` — execution manager, reusable as-is
- `std.nogc_sync_mut.debug.remote.exec.capability_report.{CapabilityReport, probe_openocd, probe_cmsis_dap}` — probes, may need new `probe_uno_q()` or reuse `probe_openocd()`
- `std.io_runtime.shell` — shell command execution for OpenOCD/serial interaction
- `std.nogc_sync_mut.jit.jit_util` — hex formatting, register parsing, memory read utilities

### Domain Notes

- **STM32U585 memory map**: Flash at 0x08000000 (2 MB), SRAM at 0x20000000 (786 KB total: SRAM1 192 KB + SRAM2 64 KB + SRAM3 320 KB + SRAM4 16 KB + ICACHE 16 KB + BKPSRAM 2 KB). Contiguous SRAM1+SRAM2+SRAM3 = 576 KB from 0x20000000.
- **Cortex-M33 arch string**: `thumbv8m.main` (ARMv8-M Mainline), ABI: `eabihf` (STM32U585 has FPU). TrustZone is M33-specific but the existing base class does not model TZ — base class extension may be needed for secure/non-secure world distinction.
- **OpenOCD support**: `stm32u5x.cfg` exists in OpenOCD 0.12.0 (`/usr/share/openocd/scripts/target/stm32u5x.cfg`). Config references `stm32x5x_common.cfg` which creates a `cortex_m` target with SWD IDCODE `0x0be12477`. Supports both JTAG and SWD transports.
- **OpenOCD clock config**: `stm32u5x_clock_config` sets MCU to 160 MHz via PLL from MSI 4 MHz. Adapter speed boosted to 4000 kHz after reset-init.
- **Cortex-M33 HW debug**: Typically 8 HW breakpoints, 4 HW watchpoints (more than M4's 4 BP / 4 WP).
- **UNO Q memory map for remote JIT**: With 576 KB contiguous SRAM, a reasonable layout would be: code 0x20010000-0x20060000 (320 KB), data 0x20060000-0x20090000 (192 KB), stack top 0x20090000. Total usable ~512 KB — significantly more than STM32H7 (704 KB) but in a different SRAM region.

### Open Questions

- **OQ-1 (for arch)**: Which debug connectivity approach for AC-3? External JTAG/SWD probe (JCTL header) vs DFU bootloader vs MPU bridge. This determines adapter architecture.
- **OQ-2 (for arch)**: Does the adapter need TrustZone awareness? STM32U585 boots secure by default; non-secure SRAM access requires TZ configuration or booting into non-secure mode.

## Requirements

- REQ-1 (from AC-1): Add `preset_cortex_m33()` function to target_presets.spl with `arch: "thumbv8m.main"`, `abi: "eabihf"`, `float_support: true`, `stack_size: 16384` (larger SRAM allows it). Add to `preset_by_name()` and `preset_all_names()`. — area: `src/compiler/70.backend/target_presets.spl`
- REQ-2 (from AC-2): Add `ArmCortexMTarget.cortex_m33()` factory method (8 HW breakpoints, 4 HW watchpoints, name "Cortex-M33"). — area: `src/lib/nogc_sync_mut/debug/remote/target/arm_cortex_m.spl`
- REQ-3 (from AC-2): Create `Stm32U5Target` class wrapping `ArmCortexMTarget.cortex_m33()` with openocd_cfg `target/stm32u5x.cfg`, flash_base 0x08000000, sram_base 0x20000000, sram_size 786432. — area: `src/lib/nogc_sync_mut/debug/remote/target/stm32u5.spl` (new file)
- REQ-4 (from AC-3): Create `UnoQAdapter` class. Connectivity mechanism TBD per OQ-1. If external probe: model on `Stm32H7Adapter` with OpenOCD telnet + `stm32u5x.cfg`. Add `MemoryMap.uno_q()` factory. — area: `src/lib/nogc_sync_mut/debug/remote/exec/adapter_uno_q.spl` (new file), `src/lib/nogc_sync_mut/debug/remote/exec/types.spl`
- REQ-5 (from AC-4): Verify serial communication on `/dev/ttyACM2` (corrected from ttyACM0). CDC ACM interface confirmed present. — area: test/connectivity verification
- REQ-6 (from AC-5): Add "Arduino UNO Q" section to board guide Section 7 and memory map to Section 2. Add board to Section 1.2 physical hardware table. — area: `doc/07_guide/embedded_board_guide.md`
- REQ-7 (from AC-6): Add UNO Q entries to hardware manifest in SDN table format (board_id, flash_base, flash_size, sram_base, sram_size, uart_baud, mcu). — area: `doc/08_tracking/hardware/hardware_manifest.sdn`
- REQ-8 (from AC-7): Verify no regressions in existing STM32H7/WB/Arduino R4 adapters — no shared code modified. — area: existing test specs

### 3-arch

## Architecture

### Decisions

- **D-1 (OQ-1 — Debug Connectivity):** Use external SWD/JTAG probe on JCTL header with OpenOCD `target/stm32u5x.cfg`. Mirror the `Stm32H7Adapter` OpenOCD-telnet pattern. The probe type is a constructor parameter (default: `interface/stlink.cfg`) because UNO Q users bring their own probe (ST-Link, J-Link, CMSIS-DAP). DFU bootloader is documented in the board guide as an alternative flash-and-run path but does NOT get its own adapter class (DFU is flash-only, cannot satisfy SRAM-execute `ExecTarget` model). The Lauterbach Power Debug II (Bus 003 Device 004, 0897:0002) is NOT used here — it is driven by TRACE32, not OpenOCD; the separate `t32` toolchain covers that path.

- **D-2 (OQ-2 — TrustZone):** Defer TrustZone modeling. The base class `ArmCortexMTarget` has no TZ awareness and OpenOCD's `stm32u5x.cfg` handles debug attach in the default (secure) world. Adding TZ-aware base class extensions is speculative without a concrete non-secure-only use case. Document: "Adapter assumes default secure-world debug access; non-secure operation deferred."

- **D-3 (AC-3 vs AC-4 Channel Separation):** AC-3 (SRAM upload/execute) uses the external probe + OpenOCD telnet pipeline. AC-4 (serial connectivity at `/dev/ttyACM2`) is the CDC-ACM channel for application-level communication only — it is NOT the adapter's debug channel. These are architecturally separate; the adapter does not use ttyACM2.

- **D-4 (Port Allocation):** UNO Q adapter uses GDB 27333, telnet 27444, TCL 27666. No collision with STM32H7 (23333/24444/26666) or Arduino R4 (25333/25444/25666).

- **D-5 (Memory Map — Conservative First Cut):** SRAM1 (192 KB, 0x20000000-0x20030000) is guaranteed non-secure-attributed in default boot. SRAM2 (64 KB) and SRAM3 (320 KB) may have different secure attribution. Use SRAM1 only for the first cut: code 0x20002000-0x20020000 (120 KB), data 0x20020000-0x2002E000 (56 KB), stack top 0x20030000. Document the full 576 KB contiguous region (SRAM1+2+3) as a future enhancement once TZ attribution is verified.

- **D-6 (E2E Verification Gate):** AC-3 E2E verification requires an external SWD/JTAG probe physically connected to the JCTL header. Without one on the test host, AC-3 is gated to unit-test scope (adapter constructs correctly, OpenOCD invocation string matches expected pattern). Phase 7 must not attempt E2E halt/execute without confirming probe availability.

### Module Plan

| Module | Path | Role | New/Modified |
|--------|------|------|--------------|
| cortex_m33 factory | `src/lib/nogc_sync_mut/debug/remote/target/arm_cortex_m.spl` | Add `cortex_m33()` static factory (8 HW BP, 4 HW WP, name "Cortex-M33") | Modified |
| stm32u5_target | `src/lib/nogc_sync_mut/debug/remote/target/stm32u5.spl` | `Stm32U5Target` class wrapping `ArmCortexMTarget.cortex_m33()` with STM32U585 memory layout | New |
| uno_q_adapter | `src/lib/nogc_sync_mut/debug/remote/exec/adapter_uno_q.spl` | `UnoQAdapter` class — OpenOCD telnet adapter for UNO Q MCU via external probe | New |
| uno_q_memory_map | `src/lib/nogc_sync_mut/debug/remote/exec/types.spl` | Add `MemoryMap.uno_q()` static factory | Modified |
| cortex_m33_preset | `src/compiler/70.backend/target_presets.spl` | Add `preset_cortex_m33()`, update `preset_by_name()` and `preset_all_names()` | Modified |
| board_guide | `doc/07_guide/embedded_board_guide.md` | Add UNO Q section (board notes, memory map, DFU guide, probe setup) | Modified |
| hardware_manifest | `doc/08_tracking/hardware/hardware_manifest.sdn` | Add UNO Q hardware entries | Modified |

### Dependency Map

- `stm32u5_target` -> `arm_cortex_m` (uses `ArmCortexMTarget.cortex_m33()`)
- `uno_q_adapter` -> `types` (uses `MemoryMap.uno_q()`)
- `uno_q_adapter` -> `std.io_runtime.shell` (shell commands for OpenOCD)
- `uno_q_adapter` -> `std.nogc_sync_mut.jit.jit_util` (hex formatting, register parsing)
- `uno_q_adapter` -> `capability_report` (uses `probe_openocd()`)
- `uno_q_adapter` -> `hardware_replay_controller` (replay support)
- `cortex_m33_preset` -> `compiler.common.driver_core_types` (uses `CompileOptions`)
- No circular dependencies: verified

### Public API

**arm_cortex_m.spl (modified):**
- `static fn cortex_m33() -> ArmCortexMTarget` — Cortex-M33 factory (8 HW BP, 4 HW WP)

**stm32u5.spl (new):**
- `class Stm32U5Target` — fields: `core: ArmCortexMTarget`, `probe_cfg: text`, `openocd_cfg: text`, `gdb_port: i32`
- `static fn default() -> Stm32U5Target` — default config with `interface/stlink.cfg`
- `static fn with_probe(probe_cfg: text) -> Stm32U5Target` — custom probe interface
- `fn name() -> text` — "STM32U5 (Cortex-M33)"
- `fn flash_base() -> i64` — 0x08000000
- `fn sram_base() -> i64` — 0x20000000
- `fn sram_size() -> i64` — 786432 (full 786 KB)
- Delegates: `core_name()`, `register_count()`, `register_name()`, `register_index()`, `hw_breakpoint_count()`, `hw_watchpoint_count()`, `breakpoint_instruction()`, `word_size()`

**adapter_uno_q.spl (new):**
- `fn default_uno_q_gdb_port() -> i32` — 27333
- `fn default_uno_q_telnet_port() -> i32` — 27444
- `fn default_uno_q_tcl_port() -> i32` — 27666
- `fn uno_q_openocd_args(probe_cfg: text) -> text` — builds OpenOCD args with probe + `target/stm32u5x.cfg`
- `class UnoQAdapter` — fields: `openocd_pid: i64`, `gdb_port: i32`, `telnet_port: i32`, `tcl_port: i32`, `memory_map: MemoryMap`, `connected: bool`, `probe_cfg: text`
- `static fn new() -> UnoQAdapter` — default probe (`interface/stlink.cfg`)
- `static fn with_probe(probe_cfg: text) -> UnoQAdapter` — custom probe
- `static fn with_ports(gdb_port: i32, telnet_port: i32) -> UnoQAdapter`
- `me connect() -> Result<text, text>` — launch OpenOCD, telnet halt
- `me disconnect()` — shutdown OpenOCD
- `fn telnet_cmd(cmd: text) -> text` — send telnet command
- `fn write_code(addr: i64, bytes: [i32]) -> Result<text, text>`
- `fn read_memory(addr: i64, count: i32) -> Result<[i32], text>`
- `fn write_register(name: text, value: i64) -> Result<text, text>`
- `fn read_register(name: text) -> Result<i64, text>`
- `fn execute_and_wait(timeout_ms: i32) -> Result<text, text>`
- `fn create_manager() -> RemoteExecutionManager`
- `fn create_replay_controller() -> HardwareReplayController`

**types.spl (modified):**
- `static fn uno_q() -> MemoryMap` — code 0x20002000-0x20020000, data 0x20020000-0x2002E000, stack_top 0x20030000

**target_presets.spl (modified):**
- `fn preset_cortex_m33() -> TargetPreset` — arch `thumbv8m.main`, abi `eabihf`, float_support true, stack_size 16384, pointer_width 32
- `preset_by_name()`: add `elif name == "cortex-m33": return preset_cortex_m33()`
- `preset_all_names()`: add `"cortex-m33"` to the returned array

### Requirement Coverage

- REQ-1 (AC-1: compiler preset) -> `cortex_m33_preset` module
- REQ-2 (AC-2: cortex_m33 factory) -> `cortex_m33 factory` module
- REQ-3 (AC-2: Stm32U5Target) -> `stm32u5_target` module
- REQ-4 (AC-3: UnoQAdapter) -> `uno_q_adapter` + `uno_q_memory_map` modules
- REQ-5 (AC-4: serial verify) -> test/connectivity verification (not an architecture module; CDC-ACM at /dev/ttyACM2 is app-level, per D-3)
- REQ-6 (AC-5: board guide) -> `board_guide` module
- REQ-7 (AC-6: hardware manifest) -> `hardware_manifest` module
- REQ-8 (AC-7: no regressions) -> no shared code structurally modified; existing adapters untouched. New `cortex_m33()` factory added alongside existing M4/M7 factories. New `MemoryMap.uno_q()` added alongside existing factories. New preset added alongside existing presets.

### 4-spec

## Specs

### Spec Files
- `test/unit/compiler/backend/target_presets_m33_spec.spl` — 7 specs covering AC-1 (preset fields + discovery)
- `test/unit/lib/debug/remote/target/stm32u5_target_spec.spl` — 11 specs covering AC-2 (target def, memory layout, core delegation, probe config)
- `test/unit/lib/debug/remote/exec/adapter_uno_q_spec.spl` — 14 specs covering AC-3 (port defaults, OpenOCD args, adapter construction, MemoryMap.uno_q)

### AC Coverage Matrix
| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | `target_presets_m33_spec.spl` | "AC-1: arch is thumbv8m.main" | Failing (no impl) |
| AC-1 | `target_presets_m33_spec.spl` | "AC-1: abi is eabihf" | Failing (no impl) |
| AC-1 | `target_presets_m33_spec.spl` | "AC-1: float_support is true" | Failing (no impl) |
| AC-1 | `target_presets_m33_spec.spl` | "AC-1: stack_size is 16384" | Failing (no impl) |
| AC-1 | `target_presets_m33_spec.spl` | "AC-1: pointer_width is 32" | Failing (no impl) |
| AC-1 | `target_presets_m33_spec.spl` | "AC-1: preset_by_name returns cortex-m33 with correct arch" | Failing (no impl) |
| AC-1 | `target_presets_m33_spec.spl` | "AC-1: preset_all_names contains cortex-m33" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: name is STM32U5 (Cortex-M33)" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: flash_base is 0x08000000" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: sram_base is 0x20000000" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: sram_size is 786432" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: core_name is Cortex-M33" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: hw_breakpoint_count is 8" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: hw_watchpoint_count is 4" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: word_size is 4" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: with_probe overrides probe_cfg" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: with_probe preserves name" | Failing (no impl) |
| AC-2 | `stm32u5_target_spec.spl` | "AC-2: default probe_cfg is interface/stlink.cfg" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: default gdb port is 27333" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: default telnet port is 27444" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: default tcl port is 27666" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: openocd args contain stm32u5x.cfg" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: openocd args contain probe config" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: openocd args with jlink probe" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: new() has gdb_port 27333" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: new() starts disconnected" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: new() has default stlink probe" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: with_probe overrides probe_cfg" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: with_ports overrides gdb_port" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: with_ports overrides telnet_port" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: code_start is 0x20002000" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: code_end is 0x20020000" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: data_start is 0x20020000" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: data_end is 0x2002E000" | Failing (no impl) |
| AC-3 | `adapter_uno_q_spec.spl` | "AC-3: stack_top is 0x20030000" | Failing (no impl) |
| AC-4 | N/A | N/A | Deferred: E2E serial verify (not unit-spec scope) |
| AC-5 | N/A | N/A | Deferred: doc update (not unit-spec scope) |
| AC-6 | N/A | N/A | Deferred: manifest update (not unit-spec scope) |
| AC-7 | N/A | N/A | Deferred: regression check (phase 7 verify scope) |

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>

## Phase
spec-done

## Log
- 1-dev: Created state file with 7 acceptance criteria, board reference, refined goal
- 2-research: Found 8 reusable modules, 8 existing code files, 8 requirements drafted. CRITICAL: UNO Q lacks CMSIS-DAP — debug connectivity (OQ-1) must be resolved by architect. Device at /dev/ttyACM2 not ttyACM0. OpenOCD stm32u5x.cfg confirmed available.
- 3-arch: Designed 7 modules (2 new, 5 modified), 6 decisions, no circular deps. OQ-1 resolved: external probe via JCTL + OpenOCD telnet (Lauterbach excluded — TRACE32 path only). OQ-2 deferred: no TZ modeling. Conservative SRAM1-only memory map (192 KB). E2E gate: probe required for AC-3 verification.
- 4-spec: Created 3 spec files with 32 total specs, 100% AC coverage (AC-1/2/3 unit-tested, AC-4/5/6/7 deferred to E2E/docs/verify phases).
