# Syscall Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/syscall_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 18 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/baremetal/syscall/result.json` |

## Scenarios

- [slow] writes string to debug console
- [slow] reads clock in centiseconds
- [slow] opens file for reading
- [slow] writes to file
- [slow] reads time since epoch
- [slow] configures UART with baud rate
- [slow] checks if UART ready to write
- [slow] checks if data available to read
- [slow] configures timer frequency
- [slow] reads current counter value
- [slow] delays for milliseconds
- [slow] delays for microseconds
- [slow] reads and writes 32-bit registers
- [slow] reads and writes 8-bit registers
- [slow] sets specific bit
- [slow] clears specific bit
- [slow] tests specific bit
- [slow] modifies bits with mask
