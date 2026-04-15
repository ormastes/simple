# Hello Riscv32 Semihost Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/hello_riscv32_semihost_spec.spl` |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/hello_riscv32_semihost/result.json` |

## Scenarios

- [slow] prints hello world message
- [slow] outputs semihost test success marker
- [slow] outputs exit code 0 message
- [slow] completes within 5 seconds
- [slow] runs 89 hardware tests on QEMU
- [slow] verifies semihosting operations
- [slow] verifies 32-bit arithmetic on real RV32
- [slow] verifies mcycle counter reading
- [slow] verifies QEMU platform (RV32, M-mode, little-endian)
- [slow] verifies interrupt cause bits are RV32 (bit 31)
- [slow] verifies stack alignment on real hardware
