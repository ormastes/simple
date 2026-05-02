# Interrupt Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/interrupt_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 29 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/baremetal/interrupt/result.json` |

## Scenarios

- [slow] enables external interrupt
- [slow] disables external interrupt
- [slow] handles out-of-range IRQ gracefully
- [slow] sets interrupt priority
- [slow] reads interrupt priority
- [slow] sets interrupt pending
- [slow] clears pending interrupt
- [slow] checks if interrupt is active
- [slow] sets vector table offset
- [slow] validates vector table address range
- [slow] enables external interrupt
- [slow] disables external interrupt
- [slow] rejects IRQ 0 (reserved)
- [slow] sets interrupt priority
- [slow] sets priority threshold
- [slow] claims pending interrupt
- [slow] completes interrupt
- [slow] enables Local APIC
- [slow] reads APIC ID
- [slow] signals EOI
- [slow] disables interrupts globally
- [slow] enables interrupts globally
- [slow] checks interrupt status
- [slow] executes function with interrupts disabled
- [slow] restores interrupt state after function
- [slow] registers interrupt handler
- [slow] unregisters interrupt handler
- [slow] dispatches to default handler for unregistered vector
- [slow] dispatches registered vector without crash
