# Linker Gen Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/linker_gen_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 57 |
| Active scenarios | 57 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/linker_gen/result.json` |

## Scenarios

- parses 1K as 1024
- parses 64K as 65536
- parses 640K as 655360
- parses 1M as 1048576
- parses 16M as 16777216
- parses 1G as 1073741824
- parses 0x0 as 0
- parses 0x100000 as 1048576
- parses 0xB8000 as VGA buffer
- parses 0xF4 as debug exit port
- read-only is 'r'
- read-write is 'rw'
- read-write-execute is 'rwx'
- read-execute is 'rx'
- formats 0 as 0x0
- formats 1MB as 0x100000
- .text section contains code
- .rodata section contains read-only data
- .data section contains initialized data
- .bss section contains uninitialized data
- multiboot must be within first 8KB
- multiboot section uses KEEP
- page alignment is 4096
- multiboot header alignment is 4
- default entry point is _start
- generates ENTRY() directive
- generates __text_start symbol
- generates __text_end symbol
- generates __bss_start symbol
- generates __bss_end symbol
- generates _end symbol
- name is QEMU x86 (i686)
- target is i686-unknown-none
- arch is i686
- lowmem starts at 0
- lowmem is 640K
- ram starts at 1MB
- ram is 16M
- VGA buffer at 0xB8000
- machine is pc
- cpu is qemu32
- debug exit iobase is 0xF4
- arch is avr
- cpu is atmega328p
- flash is 32K
- sram is 2K
- eeprom is 1K
- sram starts at 0x100
- stack is 256 bytes
- stack top is 0x8FF
- arch is msp430
- cpu is msp430g2553
- flash is 16K
- ram is 512 bytes
- flash starts at 0xC000
- ram starts at 0x200
- vector table at 0xFFE0
