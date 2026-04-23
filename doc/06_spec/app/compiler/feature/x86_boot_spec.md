# X86 Boot Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/x86_boot_spec.spl` |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/baremetal/x86_boot/result.json` |

## Scenarios

- [slow] has correct magic number
- [slow] has valid checksum
- [slow] has correct flags
- [slow] validates successfully
- [slow] allocates 64KB stack
- [slow] maintains 16-byte stack alignment
- [slow] sets up stack pointer correctly
- [slow] places multiboot header at correct address
- [slow] sets correct entry point
- [slow] boots successfully in QEMU
- [slow] handles interrupts correctly
