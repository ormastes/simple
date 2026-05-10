# Simple Language — Embedded Board Guide

A comprehensive reference for all embedded targets supported by the Simple
compiler toolchain, covering the remote JIT interpreter, baremetal OS support,
and replay/rewind debugging.

---

## 1. Supported Boards & Adapters

### 1.1 Emulators (No Hardware Required)

| Target | Adapter | Arch | QEMU Machine | Lane Status |
|--------|---------|------|-------------- |-------------|
| QEMU RV32 | `QemuRv32Adapter` | riscv32 | `virt` | **stable** |
| QEMU RV64 | `QemuRv64Adapter` | riscv64 | `virt` | in_progress |
| QEMU ARM | `QemuArmAdapter` | arm32 | `lm3s6965evb` | **stable** |
| x86_64 Direct Boot | — | x86_64 | — | **stable** |
| GHDL RV32 Semihost | `GhdlRv32Adapter` | riscv32 | VHDL simulation | host_aware |
| GHDL RV32 Mailbox | `GhdlRv32Adapter` | riscv32 | VHDL simulation | host_aware |

### 1.2 Physical Hardware

| Board / MCU | Adapter | Arch | Debug Probe | Lane Status |
|-------------|---------|------|-------------|-------------|
| STM32H7x3I-EVAL (Cortex-M7) | `Stm32H7Adapter` | arm32 | OpenOCD + ST-Link | host_aware |
| STM32WB Nucleo (Cortex-M4) | `Stm32WbAdapter` | arm32 | OpenOCD + ST-Link | host_aware |
| STM32H7 / STM32WB via TRACE32 | `Trace32Adapter` | arm32 | Lauterbach TRACE32 | host_aware |
| CH32V307 (RISC-V) | `Ch32V307Adapter` | riscv32 | WCH-Link (wlink CLI) | host_aware |
| Arduino UNO R4 WiFi (RA4M1, Cortex-M4) | `ArduinoR4Adapter` | arm32 | CMSIS-DAP / SWD | in_progress |
| ESP32 (Xtensa LX6, dual-core) | `Esp32Adapter` | xtensa | ESP-USB-Bridge / JTAG | in_progress |
| Zynq-7020 ZedBoard (FPGA) | — | arm32 | OpenOCD + Platform Cable | excluded_public |

### 1.3 Formal / Transport-Only Lanes

| Lane | Arch | Purpose |
|------|------|---------|
| `rv32_raw_injected` | riscv32 | Raw injection regression lane |
| `baremetal_runtime_check` | riscv32 | Runtime interpreter check |
| `riscv_external_formal` | riscv32 | External RTL formal proof (yosys + sby) |

---

## 2. Memory Maps

Every target has a fixed SRAM layout used by the remote JIT execution pipeline.
Defined in `src/lib/nogc_sync_mut/debug/remote/exec/types.spl`.

| Target | code_start | code_end | data_start | data_end | stack_top | Total |
|--------|------------|----------|------------|----------|-----------|-------|
| QEMU RV32 | `0x80010000` | `0x80100000` | `0x80100000` | `0x80200000` | `0x80200000` | 2 MB |
| QEMU RV64 | `0x80010000` | `0x80200000` | `0x80200000` | `0x80400000` | `0x80400000` | 4 MB |
| QEMU ARM | `0x40010000` | `0x40100000` | `0x40100000` | `0x40200000` | `0x40200000` | 2 MB |
| STM32H7 | `0x24010000` | `0x24080000` | `0x24080000` | `0x240C0000` | `0x240C0000` | 704 KB |
| STM32WB | `0x20008000` | `0x20030000` | `0x20030000` | `0x20040000` | `0x20040000` | 224 KB |
| CH32V307 | `0x20002000` | `0x20008000` | `0x20008000` | `0x2000C000` | `0x2000C000` | 40 KB |
| Arduino R4 (RA4M1) | `0x20002000` | `0x20006000` | `0x20006000` | `0x20008000` | `0x20008000` | 24 KB |
| ESP32 (DRAM) | `0x3FFB2000` | `0x3FFD0000` | `0x3FFD0000` | `0x3FFFC000` | `0x3FFFC000` | 296 KB |
| GHDL RV32 | `0x80010000` | `0x80100000` | `0x80100000` | `0x80200000` | `0x80200000` | 2 MB |

---

## 3. Remote JIT Interpreter

The remote JIT interpreter compiles Simple code on the host, uploads machine
code to the target's SRAM, executes it, and collects results — all over a debug
probe connection.

### 3.1 Pipeline

```
Simple source → CompilerBridge → native binary → CodeUploader → target SRAM
                                                                    ↓
                     ResultCollector ← result channel ← execute + halt
```

**Feature IDs:** #RJE-001 through #RJE-020

### 3.2 Connection Methods

| Method | Protocol | Adapters |
|--------|----------|----------|
| GDB-MI | GDB Machine Interface over TCP | QEMU RV32, RV64, ARM, GHDL, STM32WB |
| OpenOCD Telnet | `mww`/`mdw`/`reg` commands via `nc` | STM32H7, Arduino R4, ESP32 |
| wlink CLI | Per-command `wlink` invocations | CH32V307 |
| TRACE32 | T32GdbBridgeClient + t32rem | STM32H7, STM32WB |

### 3.3 Port Assignments

| Adapter | GDB Port | Telnet Port | TCL Port |
|---------|----------|-------------|----------|
| QEMU RV32 | 1234 | — | — |
| QEMU RV64 | 1235 | — | — |
| QEMU ARM | 1235 | — | — |
| STM32H7 | 23333 | 24444 | 26666 |
| STM32WB | 3334 | — | — |
| Arduino R4 | 25333 | 25444 | 25666 |
| ESP32 | 26333 | 26444 | 26666 |
| GHDL RV32 | 3333 | — | — |
| TRACE32 | 2331 | — | — |

### 3.4 Result Channels

| Channel | Description | Used By |
|---------|-------------|---------|
| `semihost_text` | Semihosting output capture | QEMU RV32/RV64/ARM, GHDL semihost |
| `exit_code` | Process exit code | x86_64, QEMU fallback |
| `register_readback` | Read return register after halt | STM32H7, STM32WB, CH32V307, Arduino R4, ESP32 |
| `ram_sentinel` | Magic value at known SRAM address | Hardware fallback |
| `debugger_console` | TRACE32 console output | STM32H7 TRACE32 |

### 3.5 Capability Probes

Before execution, each lane runs a lightweight probe to check tool availability.
Probes only check host tool presence — hardware detection is deferred to `connect()`.

```
probe_qemu_rv32()      → qemu-system-riscv32 + gdb-multiarch
probe_qemu_rv64()      → qemu-system-riscv64 + gdb-multiarch
probe_qemu_arm()       → qemu-system-arm + gdb-multiarch
probe_wlink()          → wlink CLI + CH32V307 board detection
probe_openocd()        → openocd
probe_trace32()        → t32rem
probe_ghdl()           → ghdl + clang + ld.lld + llvm-objcopy
probe_cmsis_dap()      → openocd (CMSIS-DAP boards)
probe_esp32()          → openocd (ESP32 USB JTAG)
probe_external_formal()→ yosys + sby + solver + ghdl + yosys-ghdl-plugin
```

### 3.6 Quick Start

```simple
use std.nogc_sync_mut.debug.remote.exec.{QemuRv32Adapter}

var adapter = QemuRv32Adapter.new()
val conn = adapter.connect()
match conn:
    Ok(msg):
        val mgr = adapter.create_manager()
        match mgr:
            Ok(manager):
                # Upload and execute code via manager
                pass_dn
            Err(e): print("manager error: {e}")
        adapter.disconnect()
    Err(e): print("connect error: {e}")
```

---

## 4. Simple Baremetal OS Support

### 4.1 SimpleOS Architecture

SimpleOS is a MDSOC-based microkernel OS written entirely in Simple, targeting
multiple architectures with a unified kernel interface.

**Supported kernel architectures** (each under `src/os/kernel/arch/`):

| Arch | Boot Entry | Console | Interrupts | Paging | Timer |
|------|-----------|---------|------------|--------|-------|
| arm32 | `boot.spl` | UART PL011 | NVIC | MPU | SysTick |
| arm64 | `crt0.S` → `boot.spl` | UART PL011 | GICv2 | 4-level PT | ARM Generic Timer |
| riscv32 | `boot.spl` | SBI console | PLIC | Sv32 | mtime |
| riscv64 | `boot.spl` | SBI console | PLIC | Sv39 | mtime |
| x86_32 | Multiboot `boot.spl` | VGA text | PIC 8259 | 2-level PT | PIT |
| x86_64 | Limine `boot.spl` | VGA text + serial | IDT + APIC | 4-level PT | HPET/TSC |

### 4.2 Baremetal Runtime Primitives

Located in `src/lib/nogc_async_mut_noalloc/baremetal/`:

| Component | File | Description |
|-----------|------|-------------|
| Startup (ARM) | `arm/startup.spl` | Vector table, `.data` copy, BSS zero |
| Startup (RV32) | `riscv32/startup.spl` | `_start`, mtvec, stack per-hart, BSS zero |
| Startup (RV64) | `riscv/startup.spl` | 64-bit variant, SBI shim |
| Allocator | `allocator.spl` | Bump, FreeList, FixedBlock, MultiPool |
| ARM NVIC | `arm/nvic.spl` | Cortex-M interrupt controller |
| RISC-V PLIC | `riscv/plic.spl` | Platform-Level Interrupt Controller |
| RISC-V SBI | `riscv/sbi.spl` | Supervisor Binary Interface shim |
| DTB Scanner | `riscv/dtb_scan.spl` | Device Tree Blob scanning |
| Cache Mgmt | `riscv/cmo.spl` | Cache management operations |
| Async Scheduler | `async/scheduler.spl` | Cooperative async for baremetal |
| Timer | `async/timer.spl` | Baremetal timer abstraction |
| Test Harness | `common/test_harness.spl` | `@platform: baremetal` test framework |

### 4.3 Semihosting

Semihosting enables I/O between target and host debugger, used for test output
and printf-style debugging on bare-metal targets.

| Arch | Instruction | Host Tools |
|------|-------------|------------|
| ARM | `BKPT` (Thumb) / `SVC` (ARM) | OpenOCD (`arm semihosting enable`), J-Link, TRACE32 |
| RV32 | `slli zero,zero,0x1f; ebreak; srai zero,zero,0x7` | OpenOCD, Ozone, TRACE32 |
| RV64 | Same magic NOP+EBREAK sequence (64-bit registers) | OpenOCD, Ozone, TRACE32 |

Configuration: `semihost_config.spl` provides `SemihostConfig` struct with
build-time `@cfg("semihost_transport", "buffered")` support.

Host-side reader: `simple semi-host-reader --smf-root=./build --transport=qemu`

### 4.4 Linker Scripts

Each architecture has a linker script defining memory regions:

| Arch | Flash/ROM | RAM | Entry | Stack |
|------|-----------|-----|-------|-------|
| ARM | `0x08000000` (1 MB) | `0x20000000` (128 KB) | `reset_handler` | 8 KB |
| RV32 | — | `0x80000000` (128 MB) | `_start` | 64 KB |
| RV64 | — | `0x80000000` (128 MB) | `_start` | 256 KB |
| x86 | — | `0x00100000` (Multiboot) | `_start` | 64 KB |

### 4.5 Cross-Compilation

The `CompilerBridge` (`compiler_bridge.spl`) handles cross-compilation for
remote JIT upload. Currently emits minimal stubs:
- ARM32: `movs r0, #0` → `[0x00, 0x20]`
- RV32: `addi a0, x0, 0` → `[0x13, 0x05, 0x00, 0x00]`

Known target triples: `riscv32-unknown-none`, `riscv64-unknown-none`,
`aarch64-unknown-none`, `x86_64-unknown-simpleos`.

---

## 5. Replay & Rewind Debugging

The replay system records execution state and enables reverse debugging on
both emulated and physical targets.

### 5.1 Architecture

```
DebugCoordinator
  └─ replay_backend: Option<DebugBackend>
       └─ ReplayEngine
            ├─ Recorder (captures events)
            ├─ Replayer (replays events)
            └─ Checkpoint (save/restore snapshots)
```

**Library:** `src/lib/nogc_sync_mut/replay/`

### 5.2 Replay Components

| Component | Path | Purpose |
|-----------|------|---------|
| ReplayEngine | `core/replay_engine.spl` | Core record/replay state machine |
| ReplayEvent | `core/replay_event.spl` | Event types for recording |
| Recorder | `process/recorder.spl` | Captures execution events |
| Replayer | `process/replayer.spl` | Replays recorded events |
| Checkpoint | `process/checkpoint.spl` | Save/restore execution snapshots |
| Codec | `codec.spl` | Event serialization/deserialization |
| AsyncTimeline | `semantic/async_timeline.spl` | Correlates spawn/yield/resume/complete per-task |
| TraceWriter | `semantic/trace_writer.spl` | Writes semantic trace events |
| TraceReader | `semantic/trace_reader.spl` | Reads semantic trace events |

### 5.3 Adapter Integration

The `HardwareReplayController` provides register/memory snapshot, checkpoint
save/restore, `reverse_step`, and `reverse_continue` — wired to all 8 hardware
adapters:

| Adapter | Replay Support |
|---------|---------------|
| QemuRv32Adapter | `create_replay_controller()` |
| QemuRv64Adapter | `create_replay_controller()` |
| QemuArmAdapter | `create_replay_controller()` |
| Stm32H7Adapter | `create_replay_controller()` |
| Stm32WbAdapter | `create_replay_controller()` |
| ArduinoR4Adapter | `create_replay_controller()` |
| Ch32V307Adapter | `create_replay_controller()` |
| GhdlRv32Adapter | `create_replay_controller()` |

### 5.4 DAP Integration

The Debug Adapter Protocol handlers support reverse debugging:
- `handle_reverse_continue` — run backward to previous breakpoint
- `handle_reverse_step` — step backward one instruction

Coordinator method: `register_replay(backend: DebugBackend)` stores the replay
backend for use by DAP handlers.

### 5.5 Replay Adapters

| Adapter | File | Target |
|---------|------|--------|
| Interpreter | `adapters/interpreter_replay.spl` | Simple interpreter |
| JIT | `adapters/jit_replay.spl` | JIT-compiled code |
| QEMU | `adapters/qemu_replay_adapter.spl` | QEMU emulated targets |
| Remote | `adapters/remote_replay.spl` | Physical hardware targets |
| Test Runner | `adapters/test_runner_replay.spl` | Test execution |

---

## 6. Lane Registry Summary

The lane registry (`lane_registry.spl`, Feature #RJE-017) is the single source
of truth for all 16 remote execution lanes.

### Lane Status Definitions

| Status | Meaning |
|--------|---------|
| **stable** | Fully tested, CI-verified, always available |
| **host_aware** | Requires specific hardware, tested when present |
| **in_progress** | Adapter exists, full pipeline not yet validated |
| **transport_only** | Transport layer only, no full execution |
| **excluded_public** | Not included in public builds |

### All 16 Lanes

| # | Lane ID | Arch | Adapter | Status |
|---|---------|------|---------|--------|
| 1 | `qemu_rv32_semihost` | riscv32 | qemu_gdb | **stable** |
| 2 | `qemu_arm_semihost` | arm32 | qemu_gdb | **stable** |
| 3 | `x86_64_direct_boot` | x86_64 | direct_boot | **stable** |
| 4 | `ch32v307_wlink` | riscv32 | wlink_cli | host_aware |
| 5 | `stm32h7_openocd` | arm32 | openocd_gdb | host_aware |
| 6 | `stm32h7_trace32` | arm32 | trace32 | host_aware |
| 7 | `ghdl_rv32_semihost` | riscv32 | ghdl_sim | host_aware |
| 8 | `ghdl_rv32_mailbox` | riscv32 | ghdl_sim | host_aware |
| 9 | `fpga_jtag_zedboard` | arm32 | openocd_gdb | excluded_public |
| 10 | `rv32_raw_injected` | riscv32 | qemu_gdb | transport_only |
| 11 | `baremetal_runtime_check` | riscv32 | qemu_gdb | transport_only |
| 12 | `riscv_external_formal` | riscv32 | external_formal | transport_only |
| 13 | `stm32wb_openocd` | arm32 | openocd_gdb | host_aware |
| 14 | `qemu_rv64_semihost` | riscv64 | qemu_gdb | in_progress |
| 15 | `arduino_r4_cmsis_dap` | arm32 | openocd_gdb | in_progress |
| 16 | `esp32_usb_jtag` | xtensa | openocd_gdb | in_progress |

---

## 7. Board-Specific Notes

### STM32H7x3I-EVAL
- **MCU:** STM32H743, Cortex-M7, 480 MHz
- **SRAM:** AXI SRAM at `0x24000000` (512 KB), code region starts at `0x24010000`
- **Debug:** ST-Link V3 via OpenOCD (`stm32h7x.cfg`)
- **Connection:** OpenOCD telnet on port 24444 + GDB on port 23333
- **Semihosting:** Supported via `arm semihosting enable`

### STM32WB Nucleo
- **MCU:** STM32WB55, Cortex-M4, 64 MHz (+ Cortex-M0+ radio core)
- **SRAM:** 256 KB at `0x20000000`, code region at `0x20008000` (avoids radio core area)
- **Debug:** ST-Link via OpenOCD (`st_nucleo_wb55.cfg`)
- **Connection:** GDB-MI on port 3334

### CH32V307
- **MCU:** WCH CH32V307, RISC-V (RV32IMAFC), 144 MHz
- **SRAM:** 64 KB at `0x20000000`, code region at `0x20002000`
- **Debug:** WCH-Link via `wlink` CLI (per-command, no persistent connection)
- **Note:** Smallest SRAM budget (40 KB usable), careful with code size

### Arduino UNO R4 WiFi
- **MCU:** Renesas RA4M1, Cortex-M4, 48 MHz
- **SRAM:** 32 KB at `0x20000000`, code region at `0x20002000`
- **Debug:** Built-in CMSIS-DAP/SWD, OpenOCD with `renesas_s7g2.cfg` (compatible)
- **Connection:** OpenOCD telnet on port 25444
- **Status:** SRAM write+readback verified, full execution pipeline in progress

### ESP32
- **MCU:** Espressif ESP32, dual-core Xtensa LX6, 240 MHz
- **SRAM:** DRAM 320 KB at `0x3FFB0000`, code region at `0x3FFB2000`
- **Debug:** Built-in USB JTAG (`esp_usb_bridge.cfg`), system OpenOCD 0.12 compatible
- **Connection:** OpenOCD telnet on port 26444
- **Note:** Only PRO_CPU targeted for execution; Xtensa architecture added to enum

### Zynq-7020 ZedBoard (FPGA)
- **SoC:** Xilinx Zynq-7020, dual Cortex-A9 + FPGA fabric
- **Debug:** Platform Cable USB II via OpenOCD JTAG
- **Status:** Excluded from public builds, used for custom RV32I CPU project
- **FPGA:** Custom RISC-V soft core, programmed via Vivado

### GHDL Simulated RV32
- **Target:** VHDL-simulated RISC-V 32-bit core
- **Modes:** Semihost (text output) and Mailbox (shared-memory communication)
- **Debug:** GDB-MI remote stub on port 3333
- **Toolchain:** Requires ghdl + clang + ld.lld + llvm-objcopy

---

## 8. File Reference

| Category | Path |
|----------|------|
| Adapters | `src/lib/nogc_sync_mut/debug/remote/exec/adapter_*.spl` |
| Types & Memory Maps | `src/lib/nogc_sync_mut/debug/remote/exec/types.spl` |
| Lane Registry | `src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl` |
| Capability Probes | `src/lib/nogc_sync_mut/debug/remote/exec/capability_report.spl` |
| Compiler Bridge | `src/lib/nogc_sync_mut/debug/remote/exec/compiler_bridge.spl` |
| Module Exports | `src/lib/nogc_sync_mut/debug/remote/exec/__init__.spl` |
| Replay Library | `src/lib/nogc_sync_mut/replay/` |
| Debug Coordinator | `src/lib/nogc_sync_mut/debug/coordinator.spl` |
| DAP Handlers | `src/lib/nogc_sync_mut/dap/dap_handlers.spl` |
| Baremetal Runtime | `src/lib/nogc_async_mut_noalloc/baremetal/` |
| Semihosting | `src/lib/nogc_async_mut_noalloc/baremetal/{arm,riscv,riscv32}/semihost.spl` |
| SimpleOS Kernel | `src/os/kernel/arch/` |
| Embedded Examples | `examples/09_embedded/` |
| QEMU OS Tests | `test/qemu/os/` |
| Integration Specs | `test/integration/remote_jit/` |
