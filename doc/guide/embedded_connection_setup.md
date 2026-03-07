# Embedded Debug Connection Setup Guide

Hardware and software setup for STM32 debugging with Trace32 (Lauterbach), ST-LINK, and OpenOCD.

## Hardware Inventory

| Device | Debugger | USB ID | Serial |
|--------|----------|--------|--------|
| **STM32H7Ax/H7Bx** | STLINK-V3 (V3J5) | `0483:374e` | `002600213137510833333639` |
| **STM32WBx0/WBx5** | ST-LINK/V2.1 (V2J39S27) | `0483:374b` | `0671FF555755846687041216` |
| *(both targets)* | Lauterbach Power Debug II | `0897:0002` | — |

**Serial ports:** `/dev/ttyACM0` (ST-LINK/V2.1 VCP), `/dev/ttyACM1` (STLINK-V3 VCP)

## Installed Software

| Tool | Version | Path |
|------|---------|------|
| `st-info` / `st-flash` | 1.8.0 | `/usr/bin/st-info` |
| `openocd` | 0.12.0 | `/usr/bin/openocd` |
| `t32marm` (Trace32) | 2013-07 | `/opt/t32/bin/pc_linux64/t32marm` |

## Trace32 (Lauterbach Power Debug II)

### Installation

Installed from `~/T32.iso` to `/opt/t32/`.

```
/opt/t32/
├── bin/pc_linux64/t32marm       # ARM debugger (32-bit targets)
├── bin/pc_linux64/t32marm64     # ARM debugger (64-bit targets)
├── config_stm32h7.t32           # Config: STM32H7 via USB
├── config_stm32wb.t32           # Config: STM32WB via USB
├── stm32h7_startup.cmm          # Startup script: STM32H7
├── stm32wb_startup.cmm          # Startup script: STM32WB
├── t32_stm32h7.sh               # Launcher: STM32H7
├── t32_stm32wb.sh               # Launcher: STM32WB
├── openocd/
│   ├── stm32h7_stlinkv3.cfg    # OpenOCD: H7 via STLINK-V3
│   └── stm32wb_stlinkv2.cfg    # OpenOCD: WB via ST-LINK/V2.1
├── demo/                        # Demo scripts and flash algorithms
└── pdf/                         # Documentation PDFs
```

### Quick Launch

```bash
# STM32H7 via Trace32
t32-stm32h7

# STM32WB via Trace32
t32-stm32wb

# Direct launch with custom config
t32marm -c /opt/t32/config_stm32h7.t32
```

### Config Files

**`/opt/t32/config_stm32h7.t32`** — USB connection config:
```ini
OS=
SYS=/opt/t32
TMP=/tmp
PBI=
USB
SCREEN=
FONT=SMALL
```

**`/opt/t32/stm32h7_startup.cmm`** — Target initialization:
```
SYStem.RESet
SYStem.CPU STM32H7A3ZI
SYStem.CONFIG.DEBUGPORTTYPE SWD
SYStem.CONFIG.CONNECTOR MIPI20T
SYStem.JtagClock 4MHz
SYStem.Option DUALPORT ON
SYStem.Option ResBreak OFF
SYStem.Option EnReset OFF
SYStem.Up
```

**`/opt/t32/stm32wb_startup.cmm`** — Target initialization:
```
SYStem.RESet
SYStem.CPU STM32WB55RG
SYStem.CONFIG.DEBUGPORTTYPE SWD
SYStem.CONFIG.CONNECTOR MIPI20T
SYStem.JtagClock 4MHz
SYStem.Option DUALPORT ON
SYStem.Option ResBreak OFF
SYStem.Option EnReset OFF
SYStem.Up
```

### Common Trace32 Commands

```
; Load ELF
Data.LOAD.Elf program.elf

; Flash programming
FLASH.ReProgram ALL
Data.LOAD.Elf program.elf
FLASH.ReProgram OFF

; Run / Break / Step
Go
Break
Step
Step.Over

; Registers
Register.view

; Memory
Data.dump 0x20000000
Data.dump 0x08000000

; Variables
Var.View %Hex variable_name
Var.Watch variable_name

; Breakpoints
Break.Set function_name
Break.Set 0x08001234
Break.List
Break.Delete /ALL

; Reset target
SYStem.Down
SYStem.Up
```

## OpenOCD + GDB

### Launch OpenOCD

```bash
# STM32H7 via STLINK-V3
openocd -f /opt/t32/openocd/stm32h7_stlinkv3.cfg

# STM32WB via ST-LINK/V2.1
openocd -f /opt/t32/openocd/stm32wb_stlinkv2.cfg

# Multiple debuggers simultaneously (use separate terminals)
openocd -f /opt/t32/openocd/stm32h7_stlinkv3.cfg &
openocd -f /opt/t32/openocd/stm32wb_stlinkv2.cfg -c "gdb_port 3334; telnet_port 4445; tcl_port 6665" &
```

### Config Files

**`/opt/t32/openocd/stm32h7_stlinkv3.cfg`**:
```tcl
source [find interface/stlink.cfg]
transport select hla_swd
hla_serial 002600213137510833333639
source [find target/stm32h7x.cfg]
adapter speed 4000
reset_config srst_only srst_nogate connect_assert_srst
```

**`/opt/t32/openocd/stm32wb_stlinkv2.cfg`**:
```tcl
source [find interface/stlink.cfg]
transport select hla_swd
hla_serial 0671FF555755846687041216
source [find target/stm32wbx.cfg]
adapter speed 4000
reset_config srst_only srst_nogate connect_assert_srst
```

### GDB Connection

```bash
# In terminal 1: start OpenOCD
openocd -f /opt/t32/openocd/stm32h7_stlinkv3.cfg

# In terminal 2: connect GDB
arm-none-eabi-gdb program.elf
(gdb) target remote :3333
(gdb) monitor reset halt
(gdb) load
(gdb) break main
(gdb) continue
```

## ST-LINK Tools

### Probe Devices

```bash
st-info --probe
```

### Flash Operations

```bash
# Flash binary
st-flash write firmware.bin 0x08000000

# Flash ELF (auto-detects address)
st-flash --format ihex write firmware.hex

# Read flash (1MB)
st-flash read dump.bin 0x08000000 0x100000

# Erase
st-flash erase

# Reset target
st-flash reset
```

### Serial Console (VCP)

```bash
# ST-LINK/V2.1 VCP (STM32WB)
screen /dev/ttyACM0 115200

# STLINK-V3 VCP (STM32H7)
screen /dev/ttyACM1 115200

# Or with minicom
minicom -D /dev/ttyACM0 -b 115200
```

## udev Rules

Located at `/etc/udev/rules.d/`:

**`49-stlink.rules`**:
```
SUBSYSTEM=="usb", ATTR{idVendor}=="0483", ATTR{idProduct}=="374b", MODE="0666", GROUP="plugdev"
SUBSYSTEM=="usb", ATTR{idVendor}=="0483", ATTR{idProduct}=="374e", MODE="0666", GROUP="plugdev"
```

**`49-lauterbach.rules`**:
```
SUBSYSTEM=="usb", ATTR{idVendor}=="0897", ATTR{idProduct}=="0002", MODE="0666", GROUP="plugdev"
SUBSYSTEM=="usb", ATTR{idVendor}=="0897", MODE="0666", GROUP="plugdev"
```

Reload after changes:
```bash
sudo udevadm control --reload-rules && sudo udevadm trigger
```

## Target Memory Maps

### STM32H7Ax/H7Bx

| Region | Address Range | Size |
|--------|--------------|------|
| Flash Bank 1 | `0x08000000 - 0x080FFFFF` | 1 MB |
| Flash Bank 2 | `0x08100000 - 0x081FFFFF` | 1 MB |
| DTCM RAM | `0x20000000 - 0x2001FFFF` | 128 KB |
| AXI SRAM | `0x24000000 - 0x2407FFFF` | 512 KB |
| SRAM1 | `0x30000000 - 0x3001FFFF` | 128 KB |
| SRAM2 | `0x30020000 - 0x3003FFFF` | 128 KB |
| Peripherals | `0x40000000 - 0x5FFFFFFF` | — |

### STM32WBx5

| Region | Address Range | Size |
|--------|--------------|------|
| Flash | `0x08000000 - 0x080FFFFF` | 1 MB |
| SRAM1 | `0x20000000 - 0x2002FFFF` | 192 KB |
| SRAM2a | `0x20030000 - 0x20037FFF` | 32 KB |
| SRAM2b | `0x20038000 - 0x2003FFFF` | 32 KB |
| Peripherals | `0x40000000 - 0x5FFFFFFF` | — |

## Troubleshooting

### USB Permission Denied
```bash
# Check user is in plugdev group
groups
# Add if missing
sudo usermod -aG plugdev $USER
# Then logout/login
```

### Trace32 libXp.so.6 Missing
A stub library was installed at `/usr/lib/x86_64-linux-gnu/libXp.so.6`. If T32 crashes on print-related features, obtain the real `libxp6` package from Lauterbach support.

### Multiple ST-LINKs — Selecting by Serial
Use `hla_serial` in OpenOCD configs to target a specific debugger. Get serials with `st-info --probe`.

### OpenOCD Connection Refused
```bash
# Check if another OpenOCD instance is running
ps aux | grep openocd
# Kill stale instances
killall openocd
```

### Trace32 Cannot Find USB Device
```bash
# Verify Lauterbach hardware is detected
lsusb | grep 0897
# Check udev rules are loaded
udevadm test /dev/bus/usb/003/005 2>&1 | grep MODE
```
