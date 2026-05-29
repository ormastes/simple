# Typed HAL Capsules Specification

Validates the typed HAL capsule module at src/lib/nogc_sync_mut/hal/ with MmioAddress, PhysAddress, DmaAddress, IrqLine types and volatile read/write operations. Uses composition-only design per D-7.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #hw-access-optimization-infra |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/pure_simple_lib_standalone_hw_plan.md |
| Source | `test/unit/lib/hal/hal_types_spec.spl` |
| Updated | 2026-05-25 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Validates the typed HAL capsule module at src/lib/nogc_sync_mut/hal/ with
MmioAddress, PhysAddress, DmaAddress, IrqLine types and volatile read/write
operations. Uses composition-only design per D-7.

## Behavior

- MmioAddress wraps base + offset + RegisterWidth
- PhysAddress wraps u64 with alignment utilities
- DmaAddress wraps PhysAddress + size, delegates to std.io.dma
- IrqLine wraps u32, IrqConfig holds trigger and priority
- Volatile ops delegate to std.io.volatile_ops

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `A` | Artifact | `N/A` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/lib/hal/hal_types/combined.log` |
| `output.log` | Log file | `build/test-artifacts/lib/hal/hal_types/output.log` |
| `run.log` | Log file | `build/test-artifacts/lib/hal/hal_types/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/lib/hal/hal_types/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/lib/hal/hal_types/stdout.log` |

## Scenarios

- AC-5: creates MmioAddress with base, offset, and width
- AC-5: RegisterWidth enum has all four widths
- AC-5: mmio_read_u32 returns a u32 value
- AC-5: mmio_write_u32 accepts MmioAddress and value
- AC-5: read with barrier returns u64
- AC-5: wraps a u64 address
- AC-5: returns true for page-aligned address
- AC-5: returns false for unaligned address
- AC-5: adds offset to physical address
- AC-5: wraps PhysAddress and size
- AC-5: allocates a DMA region of given size
- AC-5: wraps a u32 interrupt number
- AC-5: creates config with line, trigger, and priority
- AC-5: enum has all four trigger modes
- AC-5: irq_enable returns a Result
- AC-5: irq_is_pending returns bool

## Related Documentation

- **Plan:** [doc/03_plan/pure_simple_lib_standalone_hw_plan.md](doc/03_plan/pure_simple_lib_standalone_hw_plan.md)
