# X86 64 Boot Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/baremetal/x86_64_boot_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/baremetal/x86_64_boot/result.json` |

## Scenarios

- [slow] generates valid 64-bit multiboot header
- [slow] validates multiboot2 header successfully
- [slow] sets up long mode correctly
- [slow] maintains 16-byte stack alignment
- [slow] boots successfully in QEMU
- [slow] handles 64-bit interrupts
