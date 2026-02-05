# Linker Script Generation from SDN: Configuration Design

**Date**: 2026-02-05
**Status**: Design
**Related**: `doc/spec/layout.sdn`, `doc/format/smf_specification.md`

---

## Overview

Simple can generate GNU LD linker scripts from SDN configuration files. This enables:
1. **Declarative memory layout** - Define memory regions in SDN
2. **Section placement** - Control where code/data goes
3. **Symbol generation** - Export linker symbols for runtime
4. **Multi-target support** - Different layouts per target/board

---

## Configuration Levels (Priority: High to Low)

| Level | Scope | File | Use Case |
|-------|-------|------|----------|
| **Board** | Specific hardware | `boards/<board>.sdn` | Board-specific layout |
| **Target** | MCU family | `targets/<mcu>.sdn` | MCU memory map |
| **Module** | Directory | `__init__: linker_*` | Module section placement |
| **Project** | Entire project | `simple.sdn` | Default linker settings |

---

## Level 1: Project Configuration (`simple.sdn`)

### Basic Linker Settings

```sdn
[linker]
# Script generation
generate_script = true
script_path = "build/linker.ld"
script_format = "gnu"           # "gnu", "llvm", "arm"

# Default entry point
entry = "reset_handler"

# Output format
output_format = "elf32-littlearm"
output_arch = "arm"

# Stack and heap defaults
stack_size = 8K
heap_size = 16K

# Include paths for INCLUDE directive
include_paths = ["linker/", "boards/"]
```

### Memory Layout Reference

```sdn
[linker]
# Reference external layout file
memory_layout = "boards/stm32f407.sdn"

# Or inline memory definition
[linker.memory]
flash = { origin = 0x08000000, length = "1M", permissions = "rx" }
sram = { origin = 0x20000000, length = "192K", permissions = "rwx" }
ccm = { origin = 0x10000000, length = "64K", permissions = "rw" }
```

---

## Level 2: Target/Board Layout (`boards/<board>.sdn`)

### Complete Board Definition

```sdn
# boards/stm32f407_discovery.sdn

board:
    name: "STM32F407 Discovery"
    mcu: "STM32F407VG"
    clock: 168_000_000

# Memory regions
memory:
    flash:
        origin: 0x08000000
        length: 1M
        permissions: rx
        description: "Internal Flash"

    sram:
        origin: 0x20000000
        length: 128K
        permissions: rwx
        description: "Main SRAM"

    sram2:
        origin: 0x2001C000
        length: 16K
        permissions: rwx
        description: "SRAM2 (ETH/USB buffers)"

    ccm:
        origin: 0x10000000
        length: 64K
        permissions: rw
        description: "Core Coupled Memory (no DMA)"

    backup:
        origin: 0x40024000
        length: 4K
        permissions: rw
        description: "Backup SRAM"

# Section definitions
sections:
    .isr_vector:
        memory: flash
        address: 0x08000000
        align: 512
        keep: true
        input: ["*(.isr_vector)"]

    .text:
        memory: flash
        align: 4
        input: ["*(.text*)", "*(.rodata*)"]

    .init:
        memory: flash
        align: 4
        keep: true
        input: ["*(.init)", "*(.fini)"]

    .ARM.extab:
        memory: flash
        input: ["*(.ARM.extab*)"]

    .ARM.exidx:
        memory: flash
        input: ["*(.ARM.exidx*)"]

    .preinit_array:
        memory: flash
        keep: true
        input: ["*(.preinit_array*)"]

    .init_array:
        memory: flash
        keep: true
        input: ["*(.init_array*)"]

    .fini_array:
        memory: flash
        keep: true
        input: ["*(.fini_array*)"]

    .data:
        memory: sram
        load_memory: flash
        align: 4
        input: ["*(.data*)"]

    .bss:
        memory: sram
        align: 4
        type: nobits
        input: ["*(.bss*)", "*(COMMON)"]

    .heap:
        memory: sram
        size: 16K
        align: 8

    .stack:
        memory: ccm
        size: 8K
        align: 8
        direction: descending

    # DMA buffers must be in SRAM (not CCM)
    .dma_buffers:
        memory: sram2
        align: 4
        input: ["*(.dma_buffer*)"]

# Exported symbols
symbols:
    _estack: ".stack.end"
    _sidata: ".data.load_start"
    _sdata: ".data.start"
    _edata: ".data.end"
    _sbss: ".bss.start"
    _ebss: ".bss.end"
    _sheap: ".heap.start"
    _eheap: ".heap.end"
    _Min_Heap_Size: ".heap.size"
    _Min_Stack_Size: ".stack.size"

# Entry point
entry: reset_handler

# Assertions (checked at link time)
assertions:
    - expr: "_estack > _sdata"
      message: "Stack overlaps data"
    - expr: "_sheap + _Min_Heap_Size <= _eheap"
      message: "Heap overflow"
```

### Minimal Board Definition

```sdn
# boards/bluepill.sdn (STM32F103C8)

board:
    name: "Blue Pill"
    mcu: "STM32F103C8"

memory:
    flash:
        origin: 0x08000000
        length: 64K
        permissions: rx

    sram:
        origin: 0x20000000
        length: 20K
        permissions: rwx

# Use default sections
sections: default

# Override stack/heap
stack:
    size: 2K
    memory: sram

heap:
    size: 4K
    memory: sram
```

---

## Level 3: Module-Level Configuration (`__init__`)

### Section Placement for Module

```simple
# src/drivers/dma/__init__.spl
__init__:
    # All data in this module goes to .dma_buffers section
    linker_data_section = ".dma_buffers"

    # Code stays in .text
    linker_code_section = ".text"

# DMA buffer will be placed in .dma_buffers (SRAM2, not CCM)
var dma_rx_buffer: [u8; 1024]
var dma_tx_buffer: [u8; 1024]
```

### Custom Section for Module

```simple
# src/app/fast_path/__init__.spl
__init__:
    # Create custom section for hot code
    linker_code_section = ".fast_code"
    linker_data_section = ".fast_data"

    # Request CCM placement for speed
    linker_section_memory = "ccm"
```

### Function-Level Section Override

```simple
# Individual function placement
@section(".ccm_code")
fn critical_isr():
    # This function placed in CCM for speed
    ...

@section(".sram_code")
fn flash_write_routine():
    # Must run from RAM while writing flash
    ...

# Data placement
@section(".dma_buffer")
var rx_buffer: [u8; 512]

@section(".backup_sram")
var persistent_data: PersistentConfig
```

---

## Level 4: Layout Phases (Code Locality)

### Startup Optimization Layout

```sdn
# layout.sdn - 4KB page locality optimization

layout:
    page_size: 4096

    # Page budget per phase
    budgets:
        startup: 8          # 32KB max
        first_frame: 4      # 16KB max
        steady: 0           # Unlimited
        cold: 0             # Unlimited

    # Function patterns
    patterns:
        startup: ["reset_*", "init_*", "setup_*", "main"]
        first_frame: ["render_first_*", "ui_init_*"]
        cold: ["help_*", "error_*", "debug_*", "panic_*"]
        # steady is default

    # Override specific functions
    overrides:
        critical_handler: startup
        rarely_used_helper: cold

# Generated sections
linker:
    sections:
        startup: .spl.startup
        first_frame: .spl.first_frame
        steady: .spl.steady
        cold: .spl.cold

    # Section order in flash
    order: [startup, first_frame, steady, cold]
    page_align: true
```

### Phase Assignment in Code

```simple
# Explicit phase assignment
@phase(startup)
fn init_hardware():
    ...

@phase(cold)
fn print_help():
    ...

# Or via __init__
__init__:
    linker_phase_default = "steady"
```

---

## Generated Linker Script

### From `boards/stm32f407_discovery.sdn`

```ld
/* Auto-generated from boards/stm32f407_discovery.sdn */
/* Board: STM32F407 Discovery */
/* MCU: STM32F407VG */
/* Generated: 2026-02-05 */

OUTPUT_FORMAT("elf32-littlearm")
OUTPUT_ARCH(arm)
ENTRY(reset_handler)

/* Memory Regions */
MEMORY
{
    FLASH (rx)   : ORIGIN = 0x08000000, LENGTH = 1M
    SRAM (rwx)   : ORIGIN = 0x20000000, LENGTH = 128K
    SRAM2 (rwx)  : ORIGIN = 0x2001C000, LENGTH = 16K
    CCM (rw)     : ORIGIN = 0x10000000, LENGTH = 64K
    BACKUP (rw)  : ORIGIN = 0x40024000, LENGTH = 4K
}

/* Stack and Heap Sizes */
_Min_Heap_Size = 16K;
_Min_Stack_Size = 8K;

/* Sections */
SECTIONS
{
    /* Interrupt Vector Table */
    .isr_vector 0x08000000 :
    {
        . = ALIGN(512);
        KEEP(*(.isr_vector))
        . = ALIGN(4);
    } > FLASH

    /* Code */
    .text :
    {
        . = ALIGN(4);
        *(.text*)
        *(.rodata*)
        . = ALIGN(4);
    } > FLASH

    /* Init/Fini */
    .init :
    {
        KEEP(*(.init))
        KEEP(*(.fini))
    } > FLASH

    /* ARM Exception Tables */
    .ARM.extab :
    {
        *(.ARM.extab*)
    } > FLASH

    .ARM.exidx :
    {
        __exidx_start = .;
        *(.ARM.exidx*)
        __exidx_end = .;
    } > FLASH

    /* Init Arrays */
    .preinit_array :
    {
        PROVIDE_HIDDEN(__preinit_array_start = .);
        KEEP(*(.preinit_array*))
        PROVIDE_HIDDEN(__preinit_array_end = .);
    } > FLASH

    .init_array :
    {
        PROVIDE_HIDDEN(__init_array_start = .);
        KEEP(*(.init_array*))
        PROVIDE_HIDDEN(__init_array_end = .);
    } > FLASH

    .fini_array :
    {
        PROVIDE_HIDDEN(__fini_array_start = .);
        KEEP(*(.fini_array*))
        PROVIDE_HIDDEN(__fini_array_end = .);
    } > FLASH

    /* Store load address for .data */
    _sidata = LOADADDR(.data);

    /* Initialized Data (copied from Flash to SRAM) */
    .data :
    {
        . = ALIGN(4);
        _sdata = .;
        *(.data*)
        . = ALIGN(4);
        _edata = .;
    } > SRAM AT > FLASH

    /* Uninitialized Data */
    .bss (NOLOAD) :
    {
        . = ALIGN(4);
        _sbss = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        _ebss = .;
    } > SRAM

    /* DMA Buffers (must be in SRAM, not CCM) */
    .dma_buffers (NOLOAD) :
    {
        . = ALIGN(4);
        *(.dma_buffer*)
        . = ALIGN(4);
    } > SRAM2

    /* Heap */
    .heap (NOLOAD) :
    {
        . = ALIGN(8);
        _sheap = .;
        . = . + _Min_Heap_Size;
        _eheap = .;
    } > SRAM

    /* Stack (in CCM for speed) */
    .stack (NOLOAD) :
    {
        . = ALIGN(8);
        . = . + _Min_Stack_Size;
        _estack = .;
    } > CCM

    /* Backup SRAM */
    .backup_sram (NOLOAD) :
    {
        *(.backup_sram*)
    } > BACKUP

    /* Discard */
    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
    }
}

/* Assertions */
ASSERT(_estack > _sdata, "Stack overlaps data")
ASSERT(_sheap + _Min_Heap_Size <= _eheap, "Heap overflow")
ASSERT(SIZEOF(.isr_vector) <= 512, "Vector table too large")
```

---

## SDN Syntax Reference

### Memory Region

```sdn
memory:
    <name>:
        origin: <address>           # Hex or decimal
        length: <size>              # With suffix: K, M, G
        permissions: <perms>        # r, w, x combination
        description: "<text>"       # Optional
        fill: <value>               # Optional fill value
```

### Section Definition

```sdn
sections:
    <name>:
        memory: <region>            # Target memory region
        address: <addr>             # Optional fixed address
        load_memory: <region>       # Optional LMA region
        align: <bytes>              # Alignment
        type: nobits                # For .bss-like sections
        keep: true                  # KEEP() - don't garbage collect
        size: <bytes>               # For fixed-size sections
        direction: descending       # For stack (grows down)
        input: ["<pattern>", ...]   # Input section patterns
```

### Symbol Export

```sdn
symbols:
    <name>: "<expression>"
    # Expressions:
    #   ".section.start"  - Start of section
    #   ".section.end"    - End of section
    #   ".section.size"   - Size of section
    #   ".section.load_start" - Load address start
    #   "<number>"        - Literal value
```

### Assertions

```sdn
assertions:
    - expr: "<expression>"
      message: "<error message>"
```

---

## Build Integration

### Command Line

```bash
# Generate linker script from SDN
simple linker-gen boards/stm32f407.sdn -o build/linker.ld

# Build with generated script
simple build --linker-script=build/linker.ld

# Or auto-generate during build
simple build --board=stm32f407_discovery
```

### In `simple.sdn`

```sdn
[build]
board = "stm32f407_discovery"

[linker]
generate_script = true
board_file = "boards/stm32f407_discovery.sdn"
script_path = "build/linker.ld"

# Auto-regenerate on change
watch_linker_config = true
```

### Makefile Integration

```makefile
LINKER_SDN = boards/$(BOARD).sdn
LINKER_LD = build/$(BOARD).ld

$(LINKER_LD): $(LINKER_SDN)
	simple linker-gen $< -o $@

build: $(LINKER_LD)
	simple build --linker-script=$(LINKER_LD)
```

---

## Multi-Configuration Support

### Debug vs Release Layouts

```sdn
# boards/stm32f407_discovery.sdn

# Base memory (shared)
memory:
    flash: { origin: 0x08000000, length: 1M, permissions: rx }
    sram: { origin: 0x20000000, length: 128K, permissions: rwx }
    ccm: { origin: 0x10000000, length: 64K, permissions: rw }

# Profile-specific sections
profiles:
    debug:
        stack:
            size: 16K           # Larger stack for debugging
            memory: sram        # In SRAM for easier debugging

        heap:
            size: 32K

        symbols:
            _debug_mode: 1

    release:
        stack:
            size: 8K
            memory: ccm         # In CCM for speed

        heap:
            size: 16K

        symbols:
            _debug_mode: 0

        # Enable LTO sections
        sections:
            .text:
                gc_sections: true
```

```bash
# Build with profile
simple build --board=stm32f407_discovery --profile=release
```

### Bootloader + Application Layout

```sdn
# boards/stm32f407_with_bootloader.sdn

memory:
    bootloader_flash:
        origin: 0x08000000
        length: 32K
        permissions: rx

    app_flash:
        origin: 0x08008000
        length: 992K           # 1M - 32K
        permissions: rx

    sram:
        origin: 0x20000000
        length: 128K
        permissions: rwx

# Application sections start at 0x08008000
sections:
    .isr_vector:
        memory: app_flash
        address: 0x08008000
        keep: true

    .text:
        memory: app_flash

# Bootloader has separate config
# boards/stm32f407_bootloader.sdn uses bootloader_flash
```

---

## Complete Example

### Project Structure

```
project/
├── simple.sdn
├── boards/
│   ├── stm32f407_discovery.sdn
│   ├── stm32f103_bluepill.sdn
│   └── custom_board.sdn
├── layout.sdn                    # Code locality
├── src/
│   ├── main.spl
│   ├── bsp/
│   │   ├── __init__.spl
│   │   └── vectors.spl
│   └── drivers/
│       ├── __init__.spl
│       ├── dma/
│       │   ├── __init__.spl     # linker_data_section = ".dma_buffers"
│       │   └── dma.spl
│       └── flash/
│           ├── __init__.spl     # linker_code_section = ".sram_code"
│           └── flash.spl
└── build/
    └── linker.ld                 # Generated
```

### Project Config (`simple.sdn`)

```sdn
[package]
name = "firmware"
target = "cortex-m4"

[build]
board = "stm32f407_discovery"

[linker]
generate_script = true
script_path = "build/linker.ld"
layout_file = "layout.sdn"

[linker.defaults]
stack_size = 8K
heap_size = 16K
```

### DMA Driver (`src/drivers/dma/__init__.spl`)

```simple
__init__:
    # DMA buffers must be in SRAM (not CCM, no DMA access)
    linker_data_section = ".dma_buffers"
    linker_data_align = 4

    # Volatile for all DMA register access
    volatile = true
```

### Flash Driver (`src/drivers/flash/__init__.spl`)

```simple
__init__:
    # Flash write routines must run from RAM
    linker_code_section = ".sram_code"

    # Data in normal SRAM
    linker_data_section = ".data"
```

### BSP Vectors (`src/bsp/__init__.spl`)

```simple
__init__:
    # Vector table section
    linker_code_section = ".isr_vector"

    # All interrupt handlers
    interrupt_generate_vector_table = true
```

### Generated Build Command

```bash
# simple build --board=stm32f407_discovery does:
# 1. Load boards/stm32f407_discovery.sdn
# 2. Merge with layout.sdn
# 3. Process __init__ section overrides
# 4. Generate build/linker.ld
# 5. Compile with generated linker script
```

---

## Summary

### Configuration Hierarchy

```
--board=stm32f407_discovery
    └── boards/stm32f407_discovery.sdn (board memory layout)
            └── simple.sdn [linker] (project defaults)
                    └── layout.sdn (code locality)
                            └── __init__ linker_* (module sections)
                                    └── @section() (function/variable)
```

### Quick Reference

| Scope | Setting | Syntax |
|-------|---------|--------|
| **Board** | Memory regions | `boards/<board>.sdn: memory:` |
| | Sections | `boards/<board>.sdn: sections:` |
| | Symbols | `boards/<board>.sdn: symbols:` |
| **Project** | Default board | `simple.sdn: [build] board =` |
| | Stack/heap | `simple.sdn: [linker.defaults]` |
| | Output path | `simple.sdn: [linker] script_path =` |
| **Layout** | Page budget | `layout.sdn: budgets:` |
| | Phase patterns | `layout.sdn: patterns:` |
| **Module** | Code section | `__init__: linker_code_section =` |
| | Data section | `__init__: linker_data_section =` |
| **Function** | Placement | `@section(".name")` |
| | Phase | `@phase(startup)` |

### SDN to LD Mapping

| SDN | Generated LD |
|-----|--------------|
| `memory: flash: origin: 0x08000000` | `FLASH (rx) : ORIGIN = 0x08000000` |
| `sections: .text: memory: flash` | `.text : { ... } > FLASH` |
| `sections: .data: load_memory: flash` | `.data : { ... } > SRAM AT > FLASH` |
| `symbols: _estack: ".stack.end"` | `_estack = .;` (at end of stack) |
| `keep: true` | `KEEP(*(...))` |
| `align: 4` | `. = ALIGN(4);` |
