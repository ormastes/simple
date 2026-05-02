# Debug Boot Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/debug_boot_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/baremetal/debug_boot/result.json` |

## Scenarios

- can connect when qemu and gdb are available
- does not connect when qemu is missing
- does not connect when gdb is missing
- reads registers after connection
- detects null pointer crashes
- extracts stack traces
- shows register state on crash
- formats debug info
- supports x86 targets
- supports ARM targets
- supports RISC-V targets
- stores multiple breakpoints
- continues after a breakpoint
- single-steps through code
