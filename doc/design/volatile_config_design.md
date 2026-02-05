# Volatile Memory Access: Configuration Design

**Date**: 2026-02-05
**Status**: Design
**Related**: `doc/design/baremetal_features_examples.md`, `doc/design/bitfield_custom_type_design.md`

---

## Overview

Volatile memory access ensures the compiler does not optimize away reads/writes to memory-mapped I/O (MMIO) registers. This document describes how to configure volatile behavior at multiple levels.

---

## Configuration Levels (Priority: High to Low)

| Level | Scope | Syntax | Use Case |
|-------|-------|--------|----------|
| **Field** | Single field | `@volatile val x` | Individual register |
| **Struct** | All fields in struct | `@volatile struct` | Peripheral register block |
| **File** | All memory access in file | `__init__: volatile = true` | Hardware driver file |
| **Project** | All files | `simple.sdn` | Embedded firmware project |

---

## Level 1: Field-Level Volatile

### Single Variable

```simple
# Volatile variable at fixed address
@volatile val GPIO_STATUS: u32 @ 0x40020000
@volatile var GPIO_CONTROL: u32 @ 0x40020004

# Read always fetches from memory
val status = GPIO_STATUS      # Volatile read

# Write always commits to memory
GPIO_CONTROL = 0x01           # Volatile write
```

### Struct Field

```simple
struct MixedRegs:
    @volatile status: u32     # Volatile field
    config: u32               # Normal field (can be cached)
    @volatile data: u32       # Volatile field
```

---

## Level 2: Struct-Wide Volatile

### All Fields Volatile

```simple
# All fields in struct are volatile
@volatile
struct GpioRegs:
    moder: u32      # Volatile (from struct attribute)
    otyper: u32     # Volatile
    ospeedr: u32    # Volatile
    pupdr: u32      # Volatile
    idr: u32        # Volatile (input data)
    odr: u32        # Volatile (output data)

# Map to memory address
val GPIOA: ptr<GpioRegs> @ 0x40020000

# All accesses are volatile
val mode = GPIOA.moder        # Volatile read
GPIOA.odr = 0xFF              # Volatile write
```

### Mixed: Struct Volatile with Non-Volatile Override

```simple
@volatile
struct UartRegs:
    status: u32               # Volatile (from struct)
    control: u32              # Volatile (from struct)
    @nonvolatile config: u32  # NOT volatile (cached OK)
    data: u32                 # Volatile (from struct)
```

### Volatile Bitfield

```simple
@volatile
bitfield DmaControl(u32):
    enable: 1
    direction: 2
    size: 2
    priority: 2
    _reserved: 25

val DMA_CR: ptr<DmaControl> @ 0x40026000

# Entire bitfield read/write is volatile
val ctrl = *DMA_CR            # Volatile read (full u32)
ctrl.enable = 1
*DMA_CR = ctrl                # Volatile write (full u32)
```

---

## Level 3: File-Wide Volatile (`__init__`)

### All Memory Access in File

```simple
# gpio_driver.spl
__init__:
    volatile = true           # All memory access in this file is volatile

# No @volatile needed - automatic
struct GpioRegs:
    moder: u32                # Volatile (from __init__)
    otyper: u32               # Volatile
    ospeedr: u32              # Volatile
    idr: u32                  # Volatile
    odr: u32                  # Volatile

val GPIOA: ptr<GpioRegs> @ 0x40020000
val GPIOB: ptr<GpioRegs> @ 0x40020400

fn read_pin(port: ptr<GpioRegs>, pin: i32) -> bool:
    (port.idr >> pin) & 1 == 1    # Volatile read (automatic)

fn write_pin(port: ptr<GpioRegs>, pin: i32, value: bool):
    if value:
        port.odr = port.odr | (1 << pin)    # Volatile RMW
    else:
        port.odr = port.odr & ~(1 << pin)   # Volatile RMW
```

### Override in Volatile File

```simple
# hardware.spl
__init__:
    volatile = true

# Override: this struct is NOT volatile (e.g., cache for config)
@nonvolatile
struct ConfigCache:
    last_mode: u32            # Can be cached
    last_speed: u32           # Can be cached

# These are still volatile (from __init__)
val STATUS_REG: u32 @ 0x40020000    # Volatile

# This is not volatile (from @nonvolatile)
var config_cache = ConfigCache(last_mode: 0, last_speed: 0)
```

---

## Level 4: Project-Wide Configuration (`simple.sdn`)

### Entire Project Volatile (Embedded Firmware)

```sdn
# simple.sdn
[volatile]
default = false              # Normal files are not volatile

[volatile.patterns]
# Files matching these patterns are volatile by default
volatile_files = [
    "src/drivers/**/*.spl",
    "src/hal/**/*.spl",
    "src/bsp/**/*.spl"
]

[target.embedded]
volatile_default = true      # All files volatile in embedded target
```

### Per-Directory Configuration

```sdn
# simple.sdn
[volatile.directories]
"src/drivers" = true         # All files in src/drivers are volatile
"src/hal" = true             # All files in src/hal are volatile
"src/app" = false            # App code is not volatile
```

---

## Volatile Modes

### Mode Options

| Mode | Behavior | Use Case |
|------|----------|----------|
| `volatile` | Every access goes to memory | MMIO registers |
| `volatile_read` | Reads go to memory, writes can be cached | Status registers |
| `volatile_write` | Writes go to memory, reads can be cached | Control registers |
| `nonvolatile` | Normal (can be optimized) | Regular variables |

### Field-Level Modes

```simple
struct PeripheralRegs:
    @volatile_read status: u32      # Read-volatile only
    @volatile_write control: u32    # Write-volatile only
    @volatile data: u32             # Full volatile
    config: u32                     # Normal (cached OK)
```

### Struct-Level Mode

```simple
@volatile_read
struct StatusRegs:
    flag1: u32       # Read-volatile
    flag2: u32       # Read-volatile
    flag3: u32       # Read-volatile

@volatile_write
struct ControlRegs:
    cmd1: u32        # Write-volatile
    cmd2: u32        # Write-volatile
```

---

## Memory Barriers with Volatile

### Automatic Barriers

```simple
__init__:
    volatile = true
    volatile_barriers = true   # Insert barriers around volatile access

# Compiler inserts barriers automatically
val status = STATUS_REG        # barrier; read; barrier
CONTROL_REG = 0x01             # barrier; write; barrier
```

### Manual Barriers

```simple
import std.atomic.{fence, Acquire, Release}

fn read_device_data() -> u32:
    # Wait for ready
    while (STATUS_REG & READY_BIT) == 0:
        pass

    # Acquire barrier: ensure status read happens before data read
    fence(Acquire)

    # Read data
    DATA_REG

fn write_device_data(data: u32):
    # Write data
    DATA_REG = data

    # Release barrier: ensure data write completes before control
    fence(Release)

    # Signal device
    CONTROL_REG = START_BIT
```

### Barrier Configuration

```simple
__init__:
    volatile = true
    volatile_barriers = "explicit"   # No automatic barriers

# Or per-struct
@volatile(barriers: "auto")
struct GpioRegs:
    # Barriers inserted around each access
    ...

@volatile(barriers: "none")
struct FastRegs:
    # No barriers (user must add manually)
    ...
```

---

## Complete Configuration Example

### Project Configuration (`simple.sdn`)

```sdn
[package]
name = "embedded-firmware"
target = "embedded"

[volatile]
# Project-wide default
default = false

# Directory patterns
[volatile.directories]
"src/drivers" = true
"src/hal" = true
"src/bsp" = true

# File patterns (override directory)
[volatile.files]
"src/app/hardware_monitor.spl" = true

[volatile.settings]
barriers = "auto"            # "auto", "explicit", "none"
read_write_mode = "full"     # "full", "read_only", "write_only"
```

### Module Configuration (`__init__`)

```simple
# src/drivers/gpio/__init__.spl
__init__:
    volatile = true
    volatile_barriers = "auto"
    assert_default = ASSERT_STATIC   # Strict asserts for drivers

# All files in src/drivers/gpio/ inherit these settings
```

### Hardware Driver File

```simple
# src/drivers/gpio/stm32f4.spl
# Inherits: volatile = true from __init__

# Peripheral base addresses
const GPIOA_BASE: u64 = 0x40020000
const GPIOB_BASE: u64 = 0x40020400
const RCC_BASE: u64 = 0x40023800

# Register structures (volatile from __init__)
struct GpioRegs:
    moder: u32
    otyper: u32
    ospeedr: u32
    pupdr: u32
    idr: u32
    odr: u32
    bsrr: u32
    lckr: u32
    afrl: u32
    afrh: u32

# Memory-mapped registers
val GPIOA: ptr<GpioRegs> @ GPIOA_BASE
val GPIOB: ptr<GpioRegs> @ GPIOB_BASE

# RCC register for clock enable
@volatile val RCC_AHB1ENR: u32 @ RCC_BASE + 0x30

# Driver functions
fn gpio_init(port: ptr<GpioRegs>, pin: i32, mode: GpioMode):
    # All reads/writes are volatile (from __init__)
    val shift = pin * 2
    val mask = 0b11 << shift
    port.moder = (port.moder & ~mask) | ((mode as u32) << shift)

fn gpio_read(port: ptr<GpioRegs>, pin: i32) -> bool:
    (port.idr >> pin) & 1 == 1

fn gpio_write(port: ptr<GpioRegs>, pin: i32, value: bool):
    if value:
        port.bsrr = 1 << pin           # Set bit (atomic)
    else:
        port.bsrr = 1 << (pin + 16)    # Reset bit (atomic)

fn gpio_toggle(port: ptr<GpioRegs>, pin: i32):
    port.odr = port.odr xor (1 << pin)  # Read-modify-write
```

### Application File (Non-Volatile)

```simple
# src/app/main.spl
# Default: volatile = false (normal application code)

import drivers.gpio.{GPIOA, gpio_init, gpio_read, gpio_write, GpioMode}

# Local variables are NOT volatile (can be optimized)
var led_state = false
var button_pressed = false

fn main():
    # Initialize GPIO
    gpio_init(GPIOA, 5, GpioMode.Output)   # LED pin
    gpio_init(GPIOA, 0, GpioMode.Input)    # Button pin

    loop:
        # Read button (volatile access inside gpio_read)
        button_pressed = gpio_read(GPIOA, 0)

        # Local logic (can be optimized)
        if button_pressed:
            led_state = not led_state

        # Write LED (volatile access inside gpio_write)
        gpio_write(GPIOA, 5, led_state)

        delay_ms(100)
```

---

## Summary

### Configuration Hierarchy

```
simple.sdn (project)
    └── [volatile.directories] / [volatile.files]
            └── __init__ (module)
                    └── @volatile / @nonvolatile (struct)
                            └── @volatile / @nonvolatile (field)
```

### Priority (Highest to Lowest)

1. `@volatile` / `@nonvolatile` on field
2. `@volatile` / `@nonvolatile` on struct
3. `__init__: volatile = true/false` in module
4. `[volatile.files]` pattern in `simple.sdn`
5. `[volatile.directories]` in `simple.sdn`
6. `[volatile] default` in `simple.sdn`
7. Target default (`--target=embedded` → `true`)

### Quick Reference

| Scope | Volatile | Non-Volatile |
|-------|----------|--------------|
| Field | `@volatile val x` | `@nonvolatile val x` |
| Struct | `@volatile struct S` | `@nonvolatile struct S` |
| Module | `__init__: volatile = true` | `__init__: volatile = false` |
| Directory | `[volatile.directories] "path" = true` | `"path" = false` |
| Project | `[volatile] default = true` | `default = false` |
| Target | `--target=embedded` | `--target=general` |

### Volatile Modes

| Mode | Reads | Writes | Syntax |
|------|-------|--------|--------|
| Full volatile | Volatile | Volatile | `@volatile` |
| Read volatile | Volatile | Normal | `@volatile_read` |
| Write volatile | Normal | Volatile | `@volatile_write` |
| Non-volatile | Normal | Normal | `@nonvolatile` or default |
