# Linker Script Generator

> Tests the linker script generation tool for bare-metal targets. Verifies that memory layout definitions, section placement, and symbol exports are correctly translated into platform-specific linker scripts for various architectures.

<!-- sdn-diagram:id=linker_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linker_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linker_gen_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linker_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 57 | 57 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linker Script Generator

Tests the linker script generation tool for bare-metal targets. Verifies that memory layout definitions, section placement, and symbol exports are correctly translated into platform-specific linker scripts for various architectures.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/linker_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the linker script generation tool for bare-metal targets. Verifies that
memory layout definitions, section placement, and symbol exports are correctly
translated into platform-specific linker scripts for various architectures.

## Scenarios

### Memory Size Parsing

#### Kilobyte suffix

#### parses 1K as 1024

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val KB = 1024
expect(1 * KB).to_equal(1024)
```

</details>

#### parses 64K as 65536

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val KB = 1024
expect(64 * KB).to_equal(65536)
```

</details>

#### parses 640K as 655360

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Conventional memory limit.
val KB = 1024
expect(640 * KB).to_equal(655360)
```

</details>

#### Megabyte suffix

#### parses 1M as 1048576

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MB = 1048576
expect(1 * MB).to_equal(1048576)
```

</details>

#### parses 16M as 16777216

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MB = 1048576
expect(16 * MB).to_equal(16777216)
```

</details>

#### Gigabyte suffix

#### parses 1G as 1073741824

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val GB = 1073741824
expect(1 * GB).to_equal(1073741824)
```

</details>

### Hex Address Parsing

#### parses 0x0 as 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = 0x0
expect(addr).to_equal(0)
```

</details>

#### parses 0x100000 as 1048576

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1MB mark - protected mode RAM start.
val addr = 0x100000
expect(addr).to_equal(1048576)
```

</details>

#### parses 0xB8000 as VGA buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# VGA text mode buffer address.
val addr = 0xB8000
expect(addr).to_equal(753664)
```

</details>

#### parses 0xF4 as debug exit port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = 0xF4
expect(addr).to_equal(244)
```

</details>

### Memory Region Formatting

#### Permission strings

#### read-only is 'r'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perms = "r"
expect(perms).to_equal("r")
```

</details>

#### read-write is 'rw'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perms = "rw"
expect(perms).to_equal("rw")
```

</details>

#### read-write-execute is 'rwx'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perms = "rwx"
expect(perms).to_equal("rwx")
```

</details>

#### read-execute is 'rx'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val perms = "rx"
expect(perms).to_equal("rx")
```

</details>

#### Origin formatting

#### formats 0 as 0x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "0x0"
expect(expected).to_equal("0x0")
```

</details>

#### formats 1MB as 0x100000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = "0x100000"
expect(expected).to_equal("0x100000")
```

</details>

### Section Layout

#### Standard sections

#### .text section contains code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_name = ".text"
expect(section_name).to_equal(".text")
```

</details>

#### .rodata section contains read-only data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_name = ".rodata"
expect(section_name).to_equal(".rodata")
```

</details>

#### .data section contains initialized data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_name = ".data"
expect(section_name).to_equal(".data")
```

</details>

#### .bss section contains uninitialized data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_name = ".bss"
expect(section_name).to_equal(".bss")
```

</details>

#### Multiboot section

#### multiboot must be within first 8KB

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiboot spec requires header in first 8KB.
val MULTIBOOT_ADDR = 0x100000
val MULTIBOOT_LIMIT = 0x102000  # 8KB after 1MB
expect(MULTIBOOT_ADDR).to_be_less_than(MULTIBOOT_LIMIT)
```

</details>

#### multiboot section uses KEEP

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Prevent linker from discarding multiboot header.
val keep = true
expect(keep).to_equal(true)
```

</details>

#### Alignment

#### page alignment is 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val PAGE_SIZE = 4096
expect(PAGE_SIZE).to_equal(4096)
```

</details>

#### multiboot header alignment is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val MULTIBOOT_ALIGN = 4
expect(MULTIBOOT_ALIGN).to_equal(4)
```

</details>

### Entry Point

#### default entry point is _start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = "_start"
expect(entry).to_equal("_start")
```

</details>

#### generates ENTRY() directive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val directive = "ENTRY(_start)"
expect(directive).to_equal("ENTRY(_start)")
```

</details>

### Symbol Generation

#### Section boundary symbols

#### generates __text_start symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "__text_start"
expect(symbol).to_equal("__text_start")
```

</details>

#### generates __text_end symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "__text_end"
expect(symbol).to_equal("__text_end")
```

</details>

#### generates __bss_start symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "__bss_start"
expect(symbol).to_equal("__bss_start")
```

</details>

#### generates __bss_end symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "__bss_end"
expect(symbol).to_equal("__bss_end")
```

</details>

#### End of image symbol

#### generates _end symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val symbol = "_end"
expect(symbol).to_equal("_end")
```

</details>

### QEMU x86 Board Configuration

#### Board metadata

#### name is QEMU x86 (i686)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "QEMU x86 (i686)"
expect(name).to_equal("QEMU x86 (i686)")
```

</details>

#### target is i686-unknown-none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "i686-unknown-none"
expect(target).to_equal("i686-unknown-none")
```

</details>

#### arch is i686

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "i686"
expect(arch).to_equal("i686")
```

</details>

#### Memory regions

#### lowmem starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LOWMEM_ORIGIN = 0x0
expect(LOWMEM_ORIGIN).to_equal(0)
```

</details>

#### lowmem is 640K

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val LOWMEM_SIZE = 640 * 1024
expect(LOWMEM_SIZE).to_equal(655360)
```

</details>

#### ram starts at 1MB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RAM_ORIGIN = 0x100000
expect(RAM_ORIGIN).to_equal(1048576)
```

</details>

#### ram is 16M

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RAM_SIZE = 16 * 1048576
expect(RAM_SIZE).to_equal(16777216)
```

</details>

#### VGA buffer at 0xB8000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val VGA_ORIGIN = 0xB8000
expect(VGA_ORIGIN).to_equal(753664)
```

</details>

#### QEMU settings

#### machine is pc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val machine = "pc"
expect(machine).to_equal("pc")
```

</details>

#### cpu is qemu32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = "qemu32"
expect(cpu).to_equal("qemu32")
```

</details>

#### debug exit iobase is 0xF4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iobase = 0xF4
expect(iobase).to_equal(244)
```

</details>

### Arduino Uno Board Configuration

#### Board metadata

#### arch is avr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "avr"
expect(arch).to_equal("avr")
```

</details>

#### cpu is atmega328p

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = "atmega328p"
expect(cpu).to_equal("atmega328p")
```

</details>

#### Memory regions

#### flash is 32K

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val FLASH_SIZE = 32 * 1024
expect(FLASH_SIZE).to_equal(32768)
```

</details>

#### sram is 2K

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val SRAM_SIZE = 2 * 1024
expect(SRAM_SIZE).to_equal(2048)
```

</details>

#### eeprom is 1K

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val EEPROM_SIZE = 1 * 1024
expect(EEPROM_SIZE).to_equal(1024)
```

</details>

#### sram starts at 0x100

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First 256 bytes are registers and I/O.
val SRAM_ORIGIN = 0x100
expect(SRAM_ORIGIN).to_equal(256)
```

</details>

#### Stack configuration

#### stack is 256 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val STACK_SIZE = 256
expect(STACK_SIZE).to_equal(256)
```

</details>

#### stack top is 0x8FF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Top of 2KB SRAM.
val STACK_TOP = 0x8FF
expect(STACK_TOP).to_equal(2303)
```

</details>

### MSP430 LaunchPad Board Configuration

#### Board metadata

#### arch is msp430

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "msp430"
expect(arch).to_equal("msp430")
```

</details>

#### cpu is msp430g2553

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = "msp430g2553"
expect(cpu).to_equal("msp430g2553")
```

</details>

#### Memory regions

#### flash is 16K

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val FLASH_SIZE = 16 * 1024
expect(FLASH_SIZE).to_equal(16384)
```

</details>

#### ram is 512 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RAM_SIZE = 512
expect(RAM_SIZE).to_equal(512)
```

</details>

#### flash starts at 0xC000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val FLASH_ORIGIN = 0xC000
expect(FLASH_ORIGIN).to_equal(49152)
```

</details>

#### ram starts at 0x200

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val RAM_ORIGIN = 0x200
expect(RAM_ORIGIN).to_equal(512)
```

</details>

#### Interrupt vectors

#### vector table at 0xFFE0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val VECTOR_ADDR = 0xFFE0
expect(VECTOR_ADDR).to_equal(65504)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
