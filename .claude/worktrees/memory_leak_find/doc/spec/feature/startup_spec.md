# Bare-Metal Startup Code Tests

**Feature ID:** #BAREMETAL-010 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/startup_spec.spl`_

---

## Overview

Tests startup code (crt0.s equivalent) for ARM Cortex-M, x86_64, and RISC-V architectures.
Verifies vector table generation, BSS zeroing, .data section copying from flash to RAM,
stack setup, multiboot2 header validation, long mode transition on x86_64, hart initialization
on RISC-V, trap handling register save/restore, and cross-platform __spl_start_bare symbol provision.

## Syntax

```simple
# ARM: Vector table has initial SP at entry 0 and Thumb-bit reset handler at entry 1
# x86_64: Multiboot2 magic = 0xE85250D6, checks CPUID for long mode
# RISC-V: Disables interrupts, sets up trap vector, parks secondary harts in WFI
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 50 |

## Test Structure

### ARM Cortex-M Startup

#### vector table

- ✅ has correct initial SP at entry 0
- ✅ has reset handler at entry 1 with Thumb bit
- ✅ includes all 16 core exception vectors
- ✅ is aligned to 256 bytes minimum
#### reset handler

- ✅ copies .data section from flash to RAM
- ✅ zeros .bss section
- ✅ sets up stack pointer correctly
- ✅ enables FPU on Cortex-M4F
- ✅ calls __spl_start_bare
- ✅ loops forever if main returns
#### exception handlers

- ✅ has default handler for all unimplemented interrupts
- ✅ has hard fault handler that saves fault info
### x86_64 Startup

#### multiboot2 header

- ✅ has correct magic number
- ✅ has correct architecture field
- ✅ has correct checksum
- ✅ includes framebuffer tag
#### long mode check

- ✅ detects CPUID support
- ✅ detects long mode support
- ✅ fails gracefully if no long mode
#### page tables

- ✅ creates valid PML4 entry
- ✅ creates valid PDPT entry
- ✅ creates valid PD with huge pages
- ✅ identity-maps first 2MB
#### mode transition

- ✅ enables PAE in CR4
- ✅ sets LME bit in EFER
- ✅ enables paging in CR0
- ✅ loads 64-bit GDT
- ✅ jumps to 64-bit code
#### 64-bit initialization

- ✅ zeros BSS section
- ✅ sets up 64-bit stack
- ✅ calls __spl_start_bare
### RISC-V Startup

#### hart initialization

- ✅ disables interrupts on entry
- ✅ sets up trap vector
- ✅ parks secondary harts in WFI
#### primary hart setup

- ✅ saves device tree blob address
- ✅ sets up stack pointer
- ✅ configures mstatus for machine mode
#### memory initialization

- ✅ zeros BSS section
- ✅ copies .data section from flash to RAM
#### trap handling

- ✅ saves all caller-saved registers
- ✅ reads trap cause from mcause
- ✅ reads exception PC from mepc
- ✅ calls trap_handler with correct arguments
- ✅ restores registers and returns with mret
#### secondary harts

- ✅ sets up per-hart stack
- ✅ enters WFI loop
### Cross-Platform Startup

- ✅ provides __spl_start_bare symbol
- ✅ calls main with argc=0, argv=NULL
- ✅ handles main return gracefully
- ✅ aligns stack to platform requirements

