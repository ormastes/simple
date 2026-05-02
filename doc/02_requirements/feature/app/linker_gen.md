# Linker Script Generator Specification
*Source:* `test/feature/app/linker_gen_spec.spl`

## Overview



use std.text.{NL}
**Difficulty:** 3/5

## Overview

The linker script generator converts board SDN definitions into GNU LD
linker scripts for bare-metal targets. It handles:
- Memory region definitions
- Section layout
- Entry point specification
- Symbol generation

## Key Concepts

| Concept | Description |
|---------|-------------|
| Memory Region | Named memory area with origin, length, permissions |
| Section | Code/data placement with alignment and input patterns |
| Entry Point | First instruction to execute after reset |
| KEEP | Prevents section from being garbage collected |

## Implementation Notes

- Hex addresses formatted with 0x prefix
- Size suffixes: K (1024), M (1048576), G (1073741824)
- Permissions: r (read), w (write), x (execute)

## Behavior

### Memory Size Parsing

### When Kilobyte suffix

- parses 1K as 1024
- parses 64K as 65536
- parses 640K as 655360

### When Megabyte suffix

- parses 1M as 1048576
- parses 16M as 16777216

### When Gigabyte suffix

- parses 1G as 1073741824

### Hex Address Parsing

- parses 0x0 as 0
- parses 0x100000 as 1048576
- parses 0xB8000 as VGA buffer
- parses 0xF4 as debug exit port

### Memory Region Formatting

### When Permission strings

- read-only is 'r'
- read-write is 'rw'
- read-write-execute is 'rwx'
- read-execute is 'rx'

### When Origin formatting

- formats 0 as 0x0
- formats 1MB as 0x100000

### Section Layout

### When Standard sections

- .text section contains code
- .rodata section contains read-only data
- .data section contains initialized data
- .bss section contains uninitialized data

### When Multiboot section

- multiboot must be within first 8KB
- multiboot section uses KEEP

### When Alignment

- page alignment is 4096
- multiboot header alignment is 4

### Entry Point

- default entry point is _start
- generates ENTRY() directive

### Symbol Generation

### When Section boundary symbols

- generates __text_start symbol
- generates __text_end symbol
- generates __bss_start symbol
- generates __bss_end symbol

### When End of image symbol

- generates _end symbol

### QEMU x86 Board Configuration

### When Board metadata

- name is QEMU x86 (i686)
- target is i686-unknown-none
- arch is i686

### When Memory regions

- lowmem starts at 0
- lowmem is 640K
- ram starts at 1MB
- ram is 16M
- VGA buffer at 0xB8000

### When QEMU settings

- machine is pc
- cpu is qemu32
- debug exit iobase is 0xF4

### Arduino Uno Board Configuration

### When Board metadata

- arch is avr
- cpu is atmega328p

### When Memory regions

- flash is 32K
- sram is 2K
- eeprom is 1K
- sram starts at 0x100

### When Stack configuration

- stack is 256 bytes
- stack top is 0x8FF

### MSP430 LaunchPad Board Configuration

### When Board metadata

- arch is msp430
- cpu is msp430g2553

### When Memory regions

- flash is 16K
- ram is 512 bytes
- flash starts at 0xC000
- ram starts at 0x200

### When Interrupt vectors

- vector table at 0xFFE0


