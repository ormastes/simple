# Embedded Board Running Guide

How to run and test the 6 real hardware debug combos + 2 QEMU combos.

## Hardware Inventory

| # | Device | Probe | Serial | USB ID |
|---|--------|-------|--------|--------|
| 1 | STM32H7Ax | STLINK-V3 (built-in) | `002600213137510833333639` | `0483:374e` |
| 2 | STM32WBx0 | ST-LINK/V2.1 (built-in) | `0671FF555755846687041216` | `0483:374b` |
| 3 | Lauterbach Power Debug II | USB PODBUS (standalone) | — | `0897:0002` |

**Key point:** STM32 boards connect ONLY via their built-in ST-LINKs. Lauterbach T32 is a separate standalone debugger with its own JTAG target.

## Connection Matrix (8 Combos)

| # | Target | Debugger | Transport | Test File |
|---|--------|----------|-----------|-----------|
| 1 | STM32H7 | ST-Link Tools | `st-flash`/`st-info` via STLINK-V3 | `stm32h7_stlink_spec.spl` |
| 2 | STM32H7 | OpenOCD+GDB | OpenOCD `board/stm32h7x3i_eval.cfg`, GDB:3333 | `stm32h7_openocd_spec.spl` |
| 3 | STM32WB | ST-Link Tools | `st-flash`/`st-info` via ST-LINK/V2.1 | `stm32wb_stlink_spec.spl` |
| 4 | STM32WB | OpenOCD+GDB | OpenOCD `board/stm32wb5x_nucleo.cfg`, GDB:3334 | `stm32wb_openocd_spec.spl` |
| 5 | T32 target | T32 Native | `t32rem` PRACTICE commands via USB PODBUS | `t32_native_spec.spl` |
| 6 | T32 target | T32 GDB Bridge | GDB via T32 GDB server:2331 | `t32_gdb_bridge_spec.spl` |
| 7 | QEMU ARM | GDB Direct | `qemu-system-arm -s -S`, GDB:3335 | `connection_matrix_qemu_spec.spl` |
| 8 | QEMU RISC-V32 | GDB Direct | `qemu-system-riscv32 -s -S`, GDB:1234 | `qemu_unified_execution_demo.spl` |

## Prerequisites

```bash
# ST-Link tools
sudo apt install stlink-tools    # st-info, st-flash

# OpenOCD + GDB
sudo apt install openocd gdb-multiarch

# T32 — installed from ISO at /opt/t32/
ls /opt/t32/bin/pc_linux64/t32rem

# QEMU (for combos 7-8)
sudo apt install qemu-system-arm qemu-system-misc
```

## Running Each Combo

### Combo 1: STM32H7 via ST-Link Tools

Simplest path — just `st-info`/`st-flash` over the built-in STLINK-V3.

```bash
# Verify board is connected
st-info --probe
# Expected: serial 002600213137510833333639

# Read chip ID (should be 0x480)
st-info --chipid --serial=002600213137510833333639

# Flash size (2MB = 0x200000)
st-info --flash --serial=002600213137510833333639

# SRAM size
st-info --sram --serial=002600213137510833333639

# Flash a binary
st-flash --serial=002600213137510833333639 write firmware.bin 0x08000000

# Reset
st-flash --serial=002600213137510833333639 reset

# Erase all flash
st-flash --serial=002600213137510833333639 erase
```

**Capabilities:** memory read, flash write/erase, reset. No breakpoints, no stepping, no registers.

### Combo 2: STM32H7 via OpenOCD+GDB

Full debug capabilities through OpenOCD + GDB MI.

```bash
# Terminal 1: Start OpenOCD
openocd -f board/stm32h7x3i_eval.cfg -c "gdb_port 3333" -c "telnet_port 4444"

# Terminal 2: Connect GDB
gdb-multiarch firmware.elf
(gdb) target remote localhost:3333
(gdb) monitor reset halt
(gdb) load
(gdb) break main
(gdb) continue
(gdb) info reg pc
(gdb) x/4x 0x08000000
```

For serial-specific OpenOCD config, use the custom configs in `/opt/t32/openocd/`:
```bash
openocd -f /opt/t32/openocd/stm32h7_stlinkv3.cfg
```

**Capabilities:** full debug — breakpoints, stepping, registers, memory, watchpoints, stack trace.

### Combo 3: STM32WB via ST-Link Tools

Same as Combo 1 but with ST-LINK/V2.1.

```bash
# Verify board
st-info --probe
# Expected: serial 0671FF555755846687041216

# Chip ID (should be 0x495)
st-info --chipid --serial=0671FF555755846687041216

# Flash size (1MB = 0x100000)
st-info --flash --serial=0671FF555755846687041216

# SRAM size (256KB)
st-info --sram --serial=0671FF555755846687041216

# Flash + reset
st-flash --serial=0671FF555755846687041216 write firmware.bin 0x08000000
st-flash --serial=0671FF555755846687041216 reset
```

### Combo 4: STM32WB via OpenOCD+GDB

```bash
# Terminal 1: Start OpenOCD (note different port to avoid conflict with H7)
openocd -f board/stm32wb5x_nucleo.cfg -c "gdb_port 3334" -c "telnet_port 4445"

# Terminal 2: Connect GDB
gdb-multiarch firmware.elf
(gdb) target remote localhost:3334
(gdb) monitor reset halt
(gdb) load
(gdb) break main
(gdb) continue
```

### Combo 5: T32 Native (t32rem)

Direct PRACTICE commands through `t32rem` CLI. The Lauterbach Power Debug II connects to its own JTAG target.

```bash
# Verify t32rem is available
ls /opt/t32/bin/pc_linux64/t32rem

# Launch T32 GUI first (needed for t32rem to connect)
/opt/t32/bin/pc_linux64/t32marm -c /opt/t32/config_stm32h7.t32 &

# Ping T32
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 PING

# Bring target up
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 SYStem.Up

# Read PC register
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 Register.Get PC

# Halt target
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 Break

# Flash ELF
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 "FLASH.ReProgram ALL"
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 "Data.LOAD.Elf firmware.elf"
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 "FLASH.ReProgram OFF"

# Run target
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 Go

# Trace capture
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 "Trace.Arm"
```

**Capabilities:** full debug + trace capture + code coverage (T32-exclusive features).

### Combo 6: T32 GDB Bridge

GDB client connecting to T32's built-in GDB server.

```bash
# Step 1: Enable GDB server via t32rem
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 "System.Option GDBSERVER ON"
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 "GDBSERVER.PORT 2331"

# Step 2: Connect GDB
gdb-multiarch firmware.elf
(gdb) target remote localhost:2331
(gdb) info reg
(gdb) break *0x08000000
(gdb) delete 1
(gdb) disconnect

# Step 3: Disable GDB server when done
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 "System.Option GDBSERVER OFF"
```

**Capabilities:** standard GDB debug ops + T32-unique ops via PRACTICE sideband (trace, coverage).

### Combo 7: QEMU ARM Cortex-M

```bash
# Start QEMU with GDB stub
qemu-system-arm -M lm3s6965evb -nographic -s -S -kernel firmware.elf &

# Connect GDB
gdb-multiarch firmware.elf
(gdb) target remote localhost:3335
(gdb) break main
(gdb) continue
```

### Combo 8: QEMU RISC-V32

```bash
# Start QEMU with GDB stub
qemu-system-riscv32 -M virt -nographic -s -S -kernel firmware.elf &

# Connect GDB
gdb-multiarch firmware.elf
(gdb) target remote localhost:1234
(gdb) break main
(gdb) continue
```

## Test Coverage

### Unit Tests (all mock/simulation, no hardware needed)

All 23 files in `test/unit/app/debug/remote/` pass:

```bash
bin/simple test test/unit/app/debug/remote/
```

| Test File | Tests | Covers |
|-----------|-------|--------|
| `connection_matrix_spec.spl` | 21 | Matrix queries, 8 combos, target/debugger enums |
| `stlink_tools_spec.spl` | 15 | StLinkToolsClient mock: probe, chipid, flash, reset |
| `stlink_tools_adapter_spec.spl` | 12 | StLinkToolsAdapter: capabilities, unsupported ops |
| `stm32_target_spec.spl` | 8 | STM32H7/WB target defaults, serials, ports |
| `t32_native_flow_spec.spl` | 16 | T32 Native full flow: connect, flash, debug ops |
| `t32_gdb_bridge_flow_spec.spl` | 19 | T32 GDB Bridge: connect, GDB server, debug ops |
| `t32_gdb_bridge_spec.spl` | 7 | PRACTICE command formatting, GDB server config |
| `t32_gdb_adapter_spec.spl` | 10 | T32 GDB adapter config, capabilities |
| `openocd_adapter_spec.spl` | 12 | OpenOCD adapter config, capabilities |
| `openocd_stm32h7_flow_spec.spl` | 17 | STM32H7 OpenOCD full flow simulation |
| `openocd_stm32wb_flow_spec.spl` | 17 | STM32WB OpenOCD full flow simulation |
| *+ 12 more files* | ~150 | ARM targets, registers, breakpoints, frames, DWARF |

**Total: ~300+ unit tests, 0 failures.**

### Integration Tests (require real hardware)

Located in `test/integration/debug/hardware/`:

```bash
# Run all hardware integration tests (skips automatically if hardware absent)
bin/simple test test/integration/debug/hardware/
```

| Test File | Combo | Requires |
|-----------|-------|----------|
| `hardware_check.spl` | — | `st-info`, `t32rem` presence detection |
| `stm32h7_stlink_spec.spl` | 1 | STM32H7 board connected |
| `stm32h7_openocd_spec.spl` | 2 | STM32H7 + OpenOCD + GDB |
| `stm32wb_stlink_spec.spl` | 3 | STM32WB board connected |
| `stm32wb_openocd_spec.spl` | 4 | STM32WB + OpenOCD + GDB |
| `t32_native_spec.spl` | 5 | Lauterbach T32 + t32rem |
| `t32_gdb_bridge_spec.spl` | 6 | T32 + GDB server + GDB |

Each test checks hardware availability first and calls `skip()` if the device is not connected.

### What Each Integration Test Verifies

**Combo 1 (STM32H7 + ST-Link):**
- Probe detects board by serial
- Chip ID = 0x480
- Flash = 2MB, SRAM >= 128KB
- Reset succeeds

**Combo 2 (STM32H7 + OpenOCD):**
- OpenOCD starts with `board/stm32h7x3i_eval.cfg`
- GDB connects to port 3333
- `monitor reset halt` + `info reg pc` work

**Combo 3 (STM32WB + ST-Link):**
- Probe detects board by serial
- Chip ID = 0x495
- Flash = 1MB, SRAM >= 256KB
- Reset succeeds

**Combo 4 (STM32WB + OpenOCD):**
- OpenOCD starts with `board/stm32wb5x_nucleo.cfg`
- GDB connects to port 3334

**Combo 5 (T32 Native):**
- `t32rem` found at `/opt/t32/bin/pc_linux64/t32rem`
- PING succeeds
- SYStem.Up, Register.Get PC, Break all work

**Combo 6 (T32 GDB Bridge):**
- GDB server enable/disable via PRACTICE
- GDB connects to T32 port 2331
- Breakpoint set/delete via GDB

**Combos 7-8 (QEMU):** Tested in `test/integration/baremetal/` (separate existing test suite).

## Source Architecture

```
src/lib/nogc_sync_mut/
├── debug/remote/
│   ├── types.spl               # DebugConfig, Architecture, DebugError
│   ├── connection_matrix.spl   # 8-combo matrix, ConnectionSpec, queries
│   ├── target/
│   │   ├── arm_cortex_m.spl    # Base ARM Cortex-M target
│   │   ├── stm32h7.spl        # STM32H7 target (serial, openocd_cfg, gdb_port)
│   │   └── stm32wb.spl        # STM32WB target (serial, openocd_cfg, gdb_port)
│   ├── protocol/
│   │   ├── gdb_mi.spl          # GDB/MI protocol client
│   │   ├── openocd.spl         # OpenOCD process + telnet + GDB
│   │   ├── stlink_tools.spl    # st-flash/st-info CLI wrapper
│   │   └── t32_gdb_bridge.spl  # T32 + GDB server composite
│   └── feature/
│       ├── features.spl         # Feature registry
│       ├── register_openocd.spl # OpenOCD register features
│       └── register_t32_gdb.spl # T32 GDB register features
├── dap/adapter/
│   ├── mod.spl                 # DebugAdapter trait, AdapterConfig, capabilities
│   ├── openocd.spl             # OpenOCD adapter (STM32 via ST-LINK + OpenOCD)
│   ├── stlink_tools.spl        # ST-Link tools adapter (flash/reset only)
│   └── t32_gdb.spl             # T32 GDB bridge adapter
```

## Capability Matrix

| Feature | ST-Link Tools | OpenOCD+GDB | T32 Native | T32 GDB Bridge | QEMU GDB |
|---------|:---:|:---:|:---:|:---:|:---:|
| Flash write | Y | Y | Y | Y | — |
| Flash erase | Y | Y | Y | Y | — |
| Reset | Y | Y | Y | Y | Y |
| Memory read | Y | Y | Y | Y | Y |
| Memory write | — | Y | Y | Y | Y |
| Breakpoints | — | Y | Y | Y | Y |
| Stepping | — | Y | Y | Y | Y |
| Registers | — | Y | Y | Y | Y |
| Stack trace | — | Y | Y | Y | Y |
| Watchpoints | — | Y | Y | Y | Y |
| Trace capture | — | — | Y | Y | — |
| Code coverage | — | — | Y | Y | — |
| PRACTICE scripts | — | — | Y | Y | — |

## Troubleshooting

### Both ST-LINKs not detected
```bash
st-info --probe
# Should show 2 probes. If 0:
lsusb | grep 0483   # Check USB connection
sudo dmesg | tail    # Check kernel messages
```

### OpenOCD port conflict
```bash
# H7 uses 3333, WB uses 3334. If running both:
openocd -f board/stm32h7x3i_eval.cfg -c "gdb_port 3333; telnet_port 4444" &
openocd -f board/stm32wb5x_nucleo.cfg -c "gdb_port 3334; telnet_port 4445" &
```

### T32 GUI not running
`t32rem` requires the T32 GUI (`t32marm`) to be running first:
```bash
/opt/t32/bin/pc_linux64/t32marm -c /opt/t32/config_stm32h7.t32 &
sleep 2
/opt/t32/bin/pc_linux64/t32rem localhost port=20000 PING
```

### Wrong combo — T32 doesn't connect to STM32
T32 Power Debug II has its own JTAG target. It does NOT connect to the STM32 boards (those use their built-in ST-LINKs). The 6 hardware combos are:
- STM32 boards: ST-Link Tools OR OpenOCD+GDB (2 boards x 2 debuggers = 4 combos)
- T32: T32 Native OR T32 GDB Bridge (1 device x 2 debuggers = 2 combos)
