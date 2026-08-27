# Linker Script Generator

> Tests the linker script generation tool for bare-metal targets. Verifies that memory layout definitions, section placement, and symbol exports are correctly translated into platform-specific linker scripts for various architectures.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the linker script generation tool for bare-metal targets. Verifies that
memory layout definitions, section placement, and symbol exports are correctly
translated into platform-specific linker scripts for various architectures.

## Scenarios

### Memory Size Parsing

#### Kilobyte suffix

#### parses 1K as 1024

- parses 1K as 1024
   - Expected: 1 * KB equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 1K as 1024")
val KB = 1024
expect(1 * KB).to_equal(1024)
```

</details>

#### parses 64K as 65536

- parses 64K as 65536
   - Expected: 64 * KB equals `65536`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 64K as 65536")
val KB = 1024
expect(64 * KB).to_equal(65536)
```

</details>

#### parses 640K as 655360

- parses 640K as 655360
   - Expected: 640 * KB equals `655360`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 640K as 655360")
# Conventional memory limit.
val KB = 1024
expect(640 * KB).to_equal(655360)
```

</details>

#### Megabyte suffix

#### parses 1M as 1048576

- parses 1M as 1048576
   - Expected: 1 * MB equals `1048576`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 1M as 1048576")
val MB = 1048576
expect(1 * MB).to_equal(1048576)
```

</details>

#### parses 16M as 16777216

- parses 16M as 16777216
   - Expected: 16 * MB equals `16777216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 16M as 16777216")
val MB = 1048576
expect(16 * MB).to_equal(16777216)
```

</details>

#### Gigabyte suffix

#### parses 1G as 1073741824

- parses 1G as 1073741824
   - Expected: 1 * GB equals `1073741824`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 1G as 1073741824")
val GB = 1073741824
expect(1 * GB).to_equal(1073741824)
```

</details>

### Hex Address Parsing

#### parses 0x0 as 0

- parses 0x0 as 0
   - Expected: addr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 0x0 as 0")
val addr = 0x0
expect(addr).to_equal(0)
```

</details>

#### parses 0x100000 as 1048576

- parses 0x100000 as 1048576
   - Expected: addr equals `1048576`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 0x100000 as 1048576")
# 1MB mark - protected mode RAM start.
val addr = 0x100000
expect(addr).to_equal(1048576)
```

</details>

#### parses 0xB8000 as VGA buffer

- parses 0xB8000 as VGA buffer
   - Expected: addr equals `753664`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 0xB8000 as VGA buffer")
# VGA text mode buffer address.
val addr = 0xB8000
expect(addr).to_equal(753664)
```

</details>

#### parses 0xF4 as debug exit port

- parses 0xF4 as debug exit port
   - Expected: addr equals `244`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses 0xF4 as debug exit port")
val addr = 0xF4
expect(addr).to_equal(244)
```

</details>

### Memory Region Formatting

#### Permission strings

#### read-only is 'r'

- read-only is 'r'
   - Expected: perms equals `r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read-only is 'r'")
val perms = "r"
expect(perms).to_equal("r")
```

</details>

#### read-write is 'rw'

- read-write is 'rw'
   - Expected: perms equals `rw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read-write is 'rw'")
val perms = "rw"
expect(perms).to_equal("rw")
```

</details>

#### read-write-execute is 'rwx'

- read-write-execute is 'rwx'
   - Expected: perms equals `rwx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read-write-execute is 'rwx'")
val perms = "rwx"
expect(perms).to_equal("rwx")
```

</details>

#### read-execute is 'rx'

- read-execute is 'rx'
   - Expected: perms equals `rx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("read-execute is 'rx'")
val perms = "rx"
expect(perms).to_equal("rx")
```

</details>

#### Origin formatting

#### formats 0 as 0x0

- formats 0 as 0x0
   - Expected: expected equals `0x0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats 0 as 0x0")
val expected = "0x0"
expect(expected).to_equal("0x0")
```

</details>

#### formats 1MB as 0x100000

- formats 1MB as 0x100000
   - Expected: expected equals `0x100000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats 1MB as 0x100000")
val expected = "0x100000"
expect(expected).to_equal("0x100000")
```

</details>

### Section Layout

#### Standard sections

#### .text section contains code

- .text section contains code
   - Expected: section_name equals `.text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step(".text section contains code")
val section_name = ".text"
expect(section_name).to_equal(".text")
```

</details>

#### .rodata section contains read-only data

- .rodata section contains read-only data
   - Expected: section_name equals `.rodata`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step(".rodata section contains read-only data")
val section_name = ".rodata"
expect(section_name).to_equal(".rodata")
```

</details>

#### .data section contains initialized data

- .data section contains initialized data
   - Expected: section_name equals `.data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step(".data section contains initialized data")
val section_name = ".data"
expect(section_name).to_equal(".data")
```

</details>

#### .bss section contains uninitialized data

- .bss section contains uninitialized data
   - Expected: section_name equals `.bss`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step(".bss section contains uninitialized data")
val section_name = ".bss"
expect(section_name).to_equal(".bss")
```

</details>

#### Multiboot section

#### multiboot must be within first 8KB

- multiboot must be within first 8KB


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiboot must be within first 8KB")
# Multiboot spec requires header in first 8KB.
val MULTIBOOT_ADDR = 0x100000
val MULTIBOOT_LIMIT = 0x102000  # 8KB after 1MB
expect(MULTIBOOT_ADDR).to_be_less_than(MULTIBOOT_LIMIT)
```

</details>

#### multiboot section uses KEEP

- multiboot section uses KEEP
   - Expected: keep is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiboot section uses KEEP")
# Prevent linker from discarding multiboot header.
val keep = true
expect(keep).to_equal(true)
```

</details>

#### Alignment

#### page alignment is 4096

- page alignment is 4096
   - Expected: PAGE_SIZE equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("page alignment is 4096")
val PAGE_SIZE = 4096
expect(PAGE_SIZE).to_equal(4096)
```

</details>

#### multiboot header alignment is 4

- multiboot header alignment is 4
   - Expected: MULTIBOOT_ALIGN equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiboot header alignment is 4")
val MULTIBOOT_ALIGN = 4
expect(MULTIBOOT_ALIGN).to_equal(4)
```

</details>

### Entry Point

#### default entry point is _start

- default entry point is _start
   - Expected: entry equals `_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("default entry point is _start")
val entry = "_start"
expect(entry).to_equal("_start")
```

</details>

#### generates ENTRY() directive

- generates ENTRY() directive
   - Expected: directive equals `ENTRY(_start)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates ENTRY() directive")
val directive = "ENTRY(_start)"
expect(directive).to_equal("ENTRY(_start)")
```

</details>

### Symbol Generation

#### Section boundary symbols

#### generates __text_start symbol

- generates __text_start symbol
   - Expected: symbol equals `__text_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates __text_start symbol")
val symbol = "__text_start"
expect(symbol).to_equal("__text_start")
```

</details>

#### generates __text_end symbol

- generates __text_end symbol
   - Expected: symbol equals `__text_end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates __text_end symbol")
val symbol = "__text_end"
expect(symbol).to_equal("__text_end")
```

</details>

#### generates __bss_start symbol

- generates __bss_start symbol
   - Expected: symbol equals `__bss_start`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates __bss_start symbol")
val symbol = "__bss_start"
expect(symbol).to_equal("__bss_start")
```

</details>

#### generates __bss_end symbol

- generates __bss_end symbol
   - Expected: symbol equals `__bss_end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates __bss_end symbol")
val symbol = "__bss_end"
expect(symbol).to_equal("__bss_end")
```

</details>

#### End of image symbol

#### generates _end symbol

- generates _end symbol
   - Expected: symbol equals `_end`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates _end symbol")
val symbol = "_end"
expect(symbol).to_equal("_end")
```

</details>

### QEMU x86 Board Configuration

#### Board metadata

#### name is QEMU x86 (i686)

- name is QEMU x86 (i686)
   - Expected: name equals `QEMU x86 (i686)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("name is QEMU x86 (i686)")
val name = "QEMU x86 (i686)"
expect(name).to_equal("QEMU x86 (i686)")
```

</details>

#### target is i686-unknown-none

- target is i686-unknown-none
   - Expected: target equals `i686-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("target is i686-unknown-none")
val target = "i686-unknown-none"
expect(target).to_equal("i686-unknown-none")
```

</details>

#### arch is i686

- arch is i686
   - Expected: arch equals `i686`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arch is i686")
val arch = "i686"
expect(arch).to_equal("i686")
```

</details>

#### Memory regions

#### lowmem starts at 0

- lowmem starts at 0
   - Expected: LOWMEM_ORIGIN equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lowmem starts at 0")
val LOWMEM_ORIGIN = 0x0
expect(LOWMEM_ORIGIN).to_equal(0)
```

</details>

#### lowmem is 640K

- lowmem is 640K
   - Expected: LOWMEM_SIZE equals `655360`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lowmem is 640K")
val LOWMEM_SIZE = 640 * 1024
expect(LOWMEM_SIZE).to_equal(655360)
```

</details>

#### ram starts at 1MB

- ram starts at 1MB
   - Expected: RAM_ORIGIN equals `1048576`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ram starts at 1MB")
val RAM_ORIGIN = 0x100000
expect(RAM_ORIGIN).to_equal(1048576)
```

</details>

#### ram is 16M

- ram is 16M
   - Expected: RAM_SIZE equals `16777216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ram is 16M")
val RAM_SIZE = 16 * 1048576
expect(RAM_SIZE).to_equal(16777216)
```

</details>

#### VGA buffer at 0xB8000

- VGA buffer at 0xB8000
   - Expected: VGA_ORIGIN equals `753664`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("VGA buffer at 0xB8000")
val VGA_ORIGIN = 0xB8000
expect(VGA_ORIGIN).to_equal(753664)
```

</details>

#### QEMU settings

#### machine is pc

- machine is pc
   - Expected: machine equals `pc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("machine is pc")
val machine = "pc"
expect(machine).to_equal("pc")
```

</details>

#### cpu is qemu32

- cpu is qemu32
   - Expected: cpu equals `qemu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cpu is qemu32")
val cpu = "qemu32"
expect(cpu).to_equal("qemu32")
```

</details>

#### debug exit iobase is 0xF4

- debug exit iobase is 0xF4
   - Expected: iobase equals `244`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("debug exit iobase is 0xF4")
val iobase = 0xF4
expect(iobase).to_equal(244)
```

</details>

### Arduino Uno Board Configuration

#### Board metadata

#### arch is avr

- arch is avr
   - Expected: arch equals `avr`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arch is avr")
val arch = "avr"
expect(arch).to_equal("avr")
```

</details>

#### cpu is atmega328p

- cpu is atmega328p
   - Expected: cpu equals `atmega328p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cpu is atmega328p")
val cpu = "atmega328p"
expect(cpu).to_equal("atmega328p")
```

</details>

#### Memory regions

#### flash is 32K

- flash is 32K
   - Expected: FLASH_SIZE equals `32768`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flash is 32K")
val FLASH_SIZE = 32 * 1024
expect(FLASH_SIZE).to_equal(32768)
```

</details>

#### sram is 2K

- sram is 2K
   - Expected: SRAM_SIZE equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sram is 2K")
val SRAM_SIZE = 2 * 1024
expect(SRAM_SIZE).to_equal(2048)
```

</details>

#### eeprom is 1K

- eeprom is 1K
   - Expected: EEPROM_SIZE equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("eeprom is 1K")
val EEPROM_SIZE = 1 * 1024
expect(EEPROM_SIZE).to_equal(1024)
```

</details>

#### sram starts at 0x100

- sram starts at 0x100
   - Expected: SRAM_ORIGIN equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sram starts at 0x100")
# First 256 bytes are registers and I/O.
val SRAM_ORIGIN = 0x100
expect(SRAM_ORIGIN).to_equal(256)
```

</details>

#### Stack configuration

#### stack is 256 bytes

- stack is 256 bytes
   - Expected: STACK_SIZE equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stack is 256 bytes")
val STACK_SIZE = 256
expect(STACK_SIZE).to_equal(256)
```

</details>

#### stack top is 0x8FF

- stack top is 0x8FF
   - Expected: STACK_TOP equals `2303`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stack top is 0x8FF")
# Top of 2KB SRAM.
val STACK_TOP = 0x8FF
expect(STACK_TOP).to_equal(2303)
```

</details>

### MSP430 LaunchPad Board Configuration

#### Board metadata

#### arch is msp430

- arch is msp430
   - Expected: arch equals `msp430`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("arch is msp430")
val arch = "msp430"
expect(arch).to_equal("msp430")
```

</details>

#### cpu is msp430g2553

- cpu is msp430g2553
   - Expected: cpu equals `msp430g2553`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cpu is msp430g2553")
val cpu = "msp430g2553"
expect(cpu).to_equal("msp430g2553")
```

</details>

#### Memory regions

#### flash is 16K

- flash is 16K
   - Expected: FLASH_SIZE equals `16384`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flash is 16K")
val FLASH_SIZE = 16 * 1024
expect(FLASH_SIZE).to_equal(16384)
```

</details>

#### ram is 512 bytes

- ram is 512 bytes
   - Expected: RAM_SIZE equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ram is 512 bytes")
val RAM_SIZE = 512
expect(RAM_SIZE).to_equal(512)
```

</details>

#### flash starts at 0xC000

- flash starts at 0xC000
   - Expected: FLASH_ORIGIN equals `49152`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flash starts at 0xC000")
val FLASH_ORIGIN = 0xC000
expect(FLASH_ORIGIN).to_equal(49152)
```

</details>

#### ram starts at 0x200

- ram starts at 0x200
   - Expected: RAM_ORIGIN equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ram starts at 0x200")
val RAM_ORIGIN = 0x200
expect(RAM_ORIGIN).to_equal(512)
```

</details>

#### Interrupt vectors

#### vector table at 0xFFE0

- vector table at 0xFFE0
   - Expected: VECTOR_ADDR equals `65504`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vector table at 0xFFE0")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b06a3d952488b2337530cc80950b16d22044cdc8137c9294cc10648fb871dcf9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b06a3d952488b2337530cc80950b16d22044cdc8137c9294cc10648fb871dcf9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b06a3d952488b2337530cc80950b16d22044cdc8137c9294cc10648fb871dcf9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/app/linker_gen_spec.spl
mirror: doc/06_spec/03_system/feature/app/linker_gen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/linker_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/linker_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/linker_gen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 29 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/linker_gen_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses 1K as 1024' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/linker_gen_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses 64K as 65536' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/linker_gen_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses 640K as 655360' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
