# Arm32 Boot Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/arm32_boot_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/arm32_boot/result.json` |

## Scenarios

- [slow] generates valid vector table
- [slow] has correct exception count
- [slow] places vector table at aligned address
- [slow] has zero reserved entries
- [slow] initializes .data section
- [slow] zeros .bss section
- [slow] sets up stack pointer
- [slow] enables interrupts correctly
- [slow] handles interrupt priorities
- [slow] boots on LM3S6965 (Cortex-M3)
- [slow] handles SysTick interrupt
