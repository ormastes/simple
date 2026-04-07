# Startup Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/startup_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 50 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/startup/result.json` |

## Scenarios

- [slow] has correct initial SP at entry 0
- [slow] has reset handler at entry 1 with Thumb bit
- [slow] includes all 16 core exception vectors
- [slow] is aligned to 256 bytes minimum
- [slow] copies .data section from flash to RAM
- [slow] zeros .bss section
- [slow] sets up stack pointer correctly
- [slow] enables FPU on Cortex-M4F
- [slow] calls __spl_start_bare
- [slow] loops forever if main returns
- [slow] has default handler for all unimplemented interrupts
- [slow] has hard fault handler that saves fault info
- [slow] has correct magic number
- [slow] has correct architecture field
- [slow] has correct checksum
- [slow] includes framebuffer tag
- [slow] detects CPUID support
- [slow] detects long mode support
- [slow] fails gracefully if no long mode
- [slow] creates valid PML4 entry
- [slow] creates valid PDPT entry
- [slow] creates valid PD with huge pages
- [slow] identity-maps first 2MB
- [slow] enables PAE in CR4
- [slow] sets LME bit in EFER
- [slow] enables paging in CR0
- [slow] loads 64-bit GDT
- [slow] jumps to 64-bit code
- [slow] zeros BSS section
- [slow] sets up 64-bit stack
- [slow] calls __spl_start_bare
- [slow] disables interrupts on entry
- [slow] sets up trap vector
- [slow] parks secondary harts in WFI
- [slow] saves device tree blob address
- [slow] sets up stack pointer
- [slow] configures mstatus for machine mode
- [slow] zeros BSS section
- [slow] copies .data section from flash to RAM
- [slow] saves all caller-saved registers
- [slow] reads trap cause from mcause
- [slow] reads exception PC from mepc
- [slow] calls trap_handler with correct arguments
- [slow] restores registers and returns with mret
- [slow] sets up per-hart stack
- [slow] enters WFI loop
- [slow] provides __spl_start_bare symbol
- [slow] calls main with argc=0, argv=NULL
- [slow] handles main return gracefully
- [slow] aligns stack to platform requirements
