# Riscv64 Boot Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/riscv64_boot_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/baremetal/riscv64_boot/result.json` |

## Scenarios

- [slow] starts in machine mode
- [slow] sets up trap vector
- [slow] configures machine registers
- [slow] boots on virt machine
- [slow] handles traps correctly
