# Ghdl Riscv32 Semihost Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/ghdl_riscv32_semihost_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 13 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/baremetal/ghdl_riscv32_semihost/result.json` |
| `summary.txt` | Text artifact | `target/test-artifacts/feature/baremetal/ghdl_riscv32_semihost/summary.txt` |

## Scenarios

- [slow] prints hello world message
- [slow] outputs semihost test success marker
- [slow] reports test PASSED with exit code 0
- [slow] reports cycle count
- [slow] outputs SSpec header
- [slow] outputs test name
- [slow] outputs SSpec summary with 0 failures
- [slow] reports test PASSED with exit code 0
- [slow] rejects missing ELF path
- [slow] rejects malformed ELF (non-RISC-V binary)
- [slow] handles GHDL timeout gracefully
- [slow] runner produces EXIT_CODE marker on success
- [slow] runner script exists and is syntax-valid
